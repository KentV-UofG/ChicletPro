#!/usr/bin/env python
# coding: utf-8

# In[4]:


from flask import Flask, render_template, request, send_file
from io import BytesIO
import io
import zipfile
import os
import csv
import re
import shutil
import numpy as np
import pandas as pd
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.colors as mc
import matplotlib.patheffects as pe
import seaborn as sns
import time
import itertools
import scipy
from pathlib import Path
from matplotlib.backends.backend_pdf import PdfPages
from scipy.stats import ttest_ind_from_stats
from io import StringIO

pd.options.display.width = 200

from IPython.display import display, HTML
display(HTML("<style>.container { width:100% !important; }</style>"))

app = Flask(__name__, template_folder='C:\\Users\\kentv\\heatmap\\templates')
app.config['UPLOAD_FOLDER'] = 'C:\\Users\\kentv\\heatmap\\uploads'  # Ensure this folder exists

@app.route('/pdf')
def pdf_view():
    pdf_path = 'C:\\Users\\kentv\\heatmap\\images\\Logsaso.pdf'
    return send_file(pdf_path, as_attachment=False)

@app.route('/')
def index():
    return render_template('index.html')

output_bitmap_h_count = 0
output_bitmap_v_count = 0
obj_id = ''
seg_id = ''
chain_id = ''
chain_dict = {}    

@app.route('/generate_pdf', methods=['POST'])
def generate_pdf():

    ###########################################################################################################################
    #
    # Constants and default values. Do not change this section.
    # All of these variables can be set to desired values in the next section.
    
    # proton mass
    mp = 1.00727647
    
    output_csv_file  = 'HDX processed data.csv'
    output_pdf_file  = 'HDX heatmap.pdf'
    
    mutation_msg = 1

    
    p_threshold = 0.05
    Dd_threshold = 0.5       # Delta D uptake threshold for the vertical line in scatter plot
    significant_only = 1
    scatter_plot = 2020
    scatter_dir = 'scatter_plots'
    
    c1 = '#08519c' #blue 
    c2 = 'white'   #white
    c3 = '#c50f15' #red
    c_missing = '#bdbdbd' # gray;
    
    
    split_outp_by_prot = ''
    split_outp_chunks = 0
    split_outp_by_row = []
    
    plot_h = 1
    plot_v = 0
    plot_stacked  = 0
    plot_separate = 1
    
    pymol_print = 1
    pymol_dir = 'pymol_macros'
    
    #
    ###########################################################################################################################
    # --------------------------------------------------------------------------------------------------------
    #Reset Any Changed Values
    neg_col = None
    pos_col = None
    custom_colors = None
    num_col = None
    num_shades = None
    num_inputs = None
    bound1 = None
    bound2 = None
    bound3 = None
    bound4 = None
    bound5 = None
    bound6 = None
    bound7 = None
    bound8 = None
    custom_bounds = None
    custb = None
    h_or_v =  None
    font_size = 36
    font_size_title = 48
    ao = None
    dtime = None
    drop_times = None
    dpept = None
    drop_pept = None
    dpeppro = None
    dpepst = None
    dpepend = None
    dprot = None
    drop_prot = None
    dpro = None
    renumdict = None
    key1 = None
    value1 = None
    key2 = None
    value2 = None
    renumbering_dict = None
    iddict = None
    mutidWT = None
    mutidMUT = None
    mut_id_dict = None
    mutdict = None
    mutdictres = None
    mutdictwt = None
    mutation_dict = None
    slist = None
    state1_list = None
    state2_list = None
    s1 = None
    s2 = None
    state_list = None
    buffer = None
    input_csv_file = None
    pept_tick_labels = None
    time_tick_labels = None
    f_pymol = None
    zip_file = None
    download_pymol = None
    obj_id = ''
    seg_id = ''
    chain_id = ''
    chain_dict = {}
    output_bitmap_h_count = 0
    output_bitmap_v_count = 0
    output_bitmap_file = None
    # --------------------------------------------------------------------------------------------------------
    ###########################################################################################################################
    #
    # Define a few functions.

    # from https://stackoverflow.com/questions/24005221/ipython-notebook-early-exit-from-cell
    class StopExecution(Exception):
        def _render_traceback_(self):
            pass
    
    # from https://stackoverflow.com/questions/25668828/how-to-create-colour-gradient-in-python
    def colorFader(c1,c2,mix=0):   #fade (linear interpolate) from color c1 (at mix=0) to c2 (mix=1)
        c1 = c1.strip()
        c1=np.array(mc.to_rgb(c1))
        c2 = c2.strip()
        c2=np.array(mc.to_rgb(c2))
        return mc.to_hex((1-mix)*c1 + mix*c2)
   
    
    # A function to format a string
    def mk_pymol(a,b,c,d):
        #obj_id = 'obj'
        #seg_id = 'seg'
        chain_id = chain_dict.get(a, 'default_chain')  # Get the chain ID from chain_dict or use a default value
        return 'alter /{0}/{1}/{2}/{3}-{4}, b={5:.3f}'.format(obj_id, seg_id, chain_id, b, c, d)

    ######THE FOLLOWING FUNCTIONS ARE FOR CONVERTING HDExaminer FILES TO DYNAMX FORMAT#####
    
    def clean_and_divide_entry(entry):
        # Remove all letters from the entry
        cleaned_entry = re.sub(r'[a-zA-Z]', '', entry)
        if cleaned_entry:  # Check if the entry is not empty after removing letters
            # Convert to integer and divide by 60
            try:
                divided_entry = int(cleaned_entry) / 60
                return divided_entry
            except ValueError:
                return None  # Return None if conversion to integer fails
        return None  # Return None for empty or invalid entries
    
    def process_first_line(input_filecon, encoding='utf-8'):
        with open(input_filecon, 'r', encoding=encoding) as file:
            reader = csv.reader(file)
            first_line = next(reader)  # Read the first line of the CSV
            # Clean and divide each entry in the first line
            cleaned_and_divided_entries = [clean_and_divide_entry(entry) for entry in first_line if clean_and_divide_entry(entry) is not None]
            cleaned_and_divided_entries.insert(0, 0)
            #print(cleaned_and_divided_entries)
            # Get the number of valid entries
            num_entries = len(cleaned_and_divided_entries)
            return num_entries, cleaned_and_divided_entries
    
    def count_rows_after_second(input_filecon, encoding='utf-8'):
        with open(input_filecon, 'r', encoding=encoding) as file:
            reader = csv.reader(file)
            next(reader)  # Skip the first line
            next(reader)  # Skip the second line
            row_count = sum(1 for row in reader if any(row))  # Count non-empty rows
            return row_count

    def write_output_csv(input_csv_file, first_row_values, data_rows, repeated_statevalues):
        with open(input_csv_file, 'w', newline='') as file:
            writer = csv.writer(file)
            # Write the first row with preset values
            writer.writerow(first_row_values)
            # Write a spacer row after the headers
            writer.writerow([])
            # Write the data rows with blank rows as spacers
            for i in range(len(data_rows)):
                row = [''] * 15  # Create a row with 15 blank values
                if i < len(repeated_statevalues):
                    row[0] = repeated_protlist[i] #this returns a repeated gen_prot list for the protein column (likely not necessary)
                    row[1] = repeated_startvalues[i]
                    row[2] = repeated_endvalues[i]
                    row[3] = repeated_seqvalues[i]
                    #rows 4 & 5 (modification and fragment) not necessary
                    row[6] = repeated_MaxUpvalues[i]
                    row[7] = center[i] #this just repeats the center value to ensure the file works properly (likely not necessary)
                    row[8] = repeated_statevalues[i]
                    row[9] = repeated_exposurevalues[i]
                    row[10] = repeated_filelist[i] #this returns a repeated gen_file list for the file column (likely not necessary)
                    row[11] = repeated_charge[i]
                    row[12] = RTresult[i]
                    #row 13 is inten in DynamX files. There is no direct comparison in the HDExaminer file format except maybe score, however the scale is vastly different
                    row[14] = center[i]
                writer.writerow(row)
                writer.writerow([])  # Write a blank row as a spacer
                
    def gather_and_condense_columns(input_filecon, num_entries):
        # Read the CSV file
        df = pd.read_csv(input_filecon)
        # Skip the first two rows
        df = df.iloc[1:]
        # Determine the columns to gather (starting at column 7, then every 6th column)
        start_col = 7
        step = 6
        # Adjust for zero-based indexing
        columns_to_gather = [4] + [start_col + step * i for i in range(num_entries)]
        # Ensure we don't exceed the number of columns in the dataframe
        columns_to_gather = [col for col in columns_to_gather if col < len(df.columns)]
        # Gather the specified columns
        selected_columns = df.iloc[:, columns_to_gather]
        # Condense the selected columns into a single list, skipping empty values
        condensed_list = selected_columns.stack().dropna().tolist()
        return condensed_list

    def gather_D(input_filecon, num_entries):
        # Read the CSV file
        dfs = pd.read_csv(input_filecon)
        # Skip the first two rows
        dfs = dfs.iloc[1:]
        # Determine the columns to gather (starting at column 7, then every 6th column)
        start_cols = 9
        steps = 6
        # Adjust for zero-based indexing
        columns_D = [start_cols + steps * i for i in range(num_entries)]
        # Ensure we don't exceed the number of columns in the dataframe
        columns_D = [col for col in columns_D if col < len(dfs.columns)]
        # Gather the specified columns
        selected_columns_D = dfs.iloc[:, columns_D]
        # Insert 0 before converting to list for each row
        selected_columns_D.insert(0, 'Zero', 0)
        # Condense the selected columns into a single list, skipping empty values
        condensed_D = selected_columns_D.stack().dropna().tolist()
        #print(condensed_D)
        return condensed_D
    
    def create_repeated_string_list(repeated_statevalues, string_to_repeat):
        return [string_to_repeat] * len(repeated_statevalues)

    ################################################################################################
    # --------------------------------------------------------------------------------------------------------
    
    PDFgeneration = float(request.form.get('gen_pdf',0))
    
    #Determine File Type
    file_typeDoH = float(request.form['file_type'])
    if file_typeDoH == 1:
        # Read CSV file if uploaded
        input_file = request.files['csv_file']
        # Save the file temporarily
        input_filecon = os.path.join(app.config['UPLOAD_FOLDER'], input_file.filename)
        input_file.save(input_filecon)
        input_csv_file = 'output_file.csv'
        # Process the first line of the CSV file with specified encoding
        try:
            num_entries, cleaned_and_divided_entries = process_first_line(input_filecon, encoding='utf-8')
            rows_after_second = count_rows_after_second(input_filecon, encoding='utf-8')
        except UnicodeDecodeError:
            print("UnicodeDecodeError encountered with 'utf-8' encoding, trying 'iso-8859-1' encoding")
            num_entries, cleaned_and_divided_entries = process_first_line(input_filecon, encoding='iso-8859-1')
            rows_after_second = count_rows_after_second(input_filecon, encoding='iso-8859-1')
        input_statevalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '':  
                    input_statevalues.append(row[0])  
                    input_statevalues = list(filter(None, input_statevalues))
        repeated_statevalues = []
        for value in input_statevalues:
            repeated_statevalues.extend([value] * num_entries) 
        repeated_exposurevalues = []
        for i in range(len(input_statevalues)):
            repeated_exposurevalues.extend(cleaned_and_divided_entries)
        input_startvalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '': 
                    input_startvalues.append(row[1])
                    input_startvalues = list(filter(None, input_startvalues))
        repeated_startvalues = []
        for value in input_startvalues:
            repeated_startvalues.extend([value] * num_entries)
        input_endvalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '': 
                    input_endvalues.append(row[2])
                    input_endvalues = list(filter(None, input_endvalues))
        repeated_endvalues = []
        for value in input_endvalues:
            repeated_endvalues.extend([value] * num_entries)
        input_seqvalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '': 
                    input_seqvalues.append(row[3])
                    input_seqvalues = list(filter(None, input_seqvalues))
        repeated_seqvalues = []
        for value in input_seqvalues:
            repeated_seqvalues.extend([value] * num_entries)
        input_MaxUpvalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '': 
                    input_MaxUpvalues.append(row[6])
                    input_MaxUpvalues = list(filter(None, input_MaxUpvalues))
        repeated_MaxUpvalues = []
        for value in input_MaxUpvalues:
            repeated_MaxUpvalues.extend([value] * num_entries)
        input_chargevalues = []
        with open(input_filecon, 'r') as file:
            reader = csv.reader(file)
            for _ in range(2):
                next(reader)
            for row in reader:
                if row != '': 
                    input_chargevalues.append(row[5])
                    input_chargevalues = list(filter(None, input_chargevalues))
        repeated_chargevalues = []
        for value in input_chargevalues:
            repeated_chargevalues.extend([value] * num_entries)
        # Preset values for the first row in the output CSV
        first_row_values = ['Protein', 'Start', 'End', 'Sequence', 'Modification',
                           'Fragment', 'MaxUptake', 'MHP', 'State', 'Exposure',
                           'File', 'z', 'RT', 'Inten', 'Center']
        # Fill data_rows with rows of 15 blank values, based on the length of repeated_values
        data_rows = [[''] * 15 for _ in range(len(repeated_statevalues))]
        RTresult = gather_and_condense_columns(input_filecon, num_entries)
        center = gather_D(input_filecon, num_entries)
        string_to_repeat = 'gen_prot' 
        repeated_protlist = create_repeated_string_list(repeated_statevalues, string_to_repeat)
        string_to_repeat = 'gen_file'
        repeated_filelist = create_repeated_string_list(repeated_statevalues, string_to_repeat)
        string_to_repeat = '1'
        repeated_charge = create_repeated_string_list(repeated_statevalues, string_to_repeat)
        # Write to the output CSV file
        write_output_csv(input_csv_file, first_row_values, data_rows, repeated_statevalues)
        # Output the results
        print(f'Number of exposures: {num_entries}')
        print(f'Exposure Times (converted to min): {cleaned_and_divided_entries}')
        print(f'Number of rows after the second row (peptides): {rows_after_second}')
    else:
        # Read CSV file if uploaded
        input_csv_file = request.files['csv_file']

    # --------------------------------------------------------------------------------------------------------
    #Gather user inputs

    #For Woods Plots
    color_by_heatmap = float(request.form.get('colorbyheatmap',0))
    colcutopt = float(request.form.get('colcutopt',0))
    if colcutopt == 1:
        colcutoff = float(request.form.get('colcutoff',0.5))
    else:
        colcutoff = 0.5
    woodsdimen = float(request.form.get('woodsdimen',0))
    if woodsdimen == 1:
        woodsx = float(request.form.get('woodsx',20))
        woodsy = float(request.form.get('woodsy',6))
    else:
        woodsx = 20
        woodsy = 6
    woodscol = float(request.form.get('woodscol',0))
    if woodscol == 1:
        woodscolpos = request.form.get('woodscolpos','red')
        woodscolneu = request.form.get('woodscolneu','white')
        woodscolneg = request.form.get('woodscolneg','blue')
    else:
        woodscolpos = 'red'
        woodscolneu = 'white'
        woodscolneg = 'blue'
    nolines = float(request.form.get('nolines', 0))
    
    #Set font sizes
    font_size = float(request.form['font_size'])
    font_size_title = float(request.form['font_size_title'])
    #Set horizontal or vertical plots
    h_or_v = float(request.form['h_or_v'])
    if h_or_v == 1:
        plot_v = 0
        plot_h = 1
        plot_w = 0
    elif h_or_v == 2:
        plot_v = 1
        plot_h = 0
        plot_w = 0
    elif h_or_v == 3:
        plot_v = 0
        plot_h = 0
        plot_w = 1
    zerobound = float(request.form.get('zerobound', 0))
    #Volcano Plotting?
    scatter_plot = request.form.get('scatterplot', 2020)
    if scatter_plot != 2020:
        scatter_plot = float(scatter_plot)
    p_threshold = request.form.get('pthresh', 0.05)
    if p_threshold == '':
        p_threshold = 0.05
    if p_threshold != 0.05 and p_threshold != '':
        p_threshold = float(p_threshold)
    #Choose between setting MaxRange/#Shades and CustomColours/Bounds
    custb = float(request.form['option'])
    if custb == 3:
        max_range = float(request.form['max_range'])
        max_range = round(max_range, 1)
        num_shades = float(request.form['num_shades'])
        num_shades = round(num_shades)
        alt_col = float(request.form.get('alt_col_RS', 0))
        if alt_col == 1:
            c1 = request.form.get('negcolRS','#08519c').strip()
            c3 = request.form.get('poscolRS','#c50f15').strip()
    elif custb == 2:
        num_shades = 7
        alt_col = float(request.form.get('alt_col_DD', 0))
        if alt_col == 1:
            c1 = request.form.get('negcolDD','#08519c')
            c3 = request.form.get('poscolDD','#c50f15')
    elif custb == 1:
        max_range = None
        custom_bounds = []
        numinputs = 8 #how many to try and read
        for i in range(1, numinputs + 1):
            nb = request.form.get(f'inputbn{i}', 2020).strip()
            pb = request.form.get(f'inputbp{i}', 2020).strip()
            if nb == 2020 or nb == '':
                break
            nb = float(nb)
            pb = float(pb)
            custom_bounds.extend([nb, pb])
            if zerobound == 1:
                custom_bounds.append(0)
        numinputs = len(custom_bounds) // 2
        if zerobound == 1:
            numinputs == numinputs + 1
        #Gather Colour Choices 
        neg_col = float(request.form['neg_col'])
        pos_col = float(request.form['pos_col'])
        num_col = 2*numinputs - 1
        numbshades = numinputs-1
        #Define negative colours - dark, medium, and light
        if neg_col == 1: #red
            dcoln = '#990000'
        elif neg_col == 2: #blue
            dcoln = '#08519c'
        elif neg_col == 3: #green
            dcoln = '#006600'
        elif neg_col == 4: #yellow
            dcoln = '#e69b00'
        elif neg_col == 5: #purple
            dcoln = '#643d6e'
        elif neg_col == 6: #black
            dcoln = '#000000'
        #Define positive colours - dark, medium, and light
        if pos_col == 1: #blue
            dcolp = '#08519c'
        elif pos_col == 2: #red
            dcolp = '#990000'
        elif pos_col == 3: #green
            dcolp = '#006600'
        elif pos_col == 4: #yellow
            dcolp = '#e69b00'
        elif pos_col == 5: #purple
            dcolp = '#643d6e'
        elif pos_col == 6: #black
            dcolp = '#000000'
        c1 = dcoln
        c2 = '#FFFFFF'
        c3 = dcolp
        col_mid = [mc.to_hex(c2)]
        cols1 = [colorFader(c1,c2,x/numbshades) for x in range(numbshades+1)]
        cols2 = [colorFader(c2,c3,x/numbshades) for x in range(numbshades+1)]
        if zerobound == 1:
            custom_colors = cols1[:-1] +cols2[1:]
        if zerobound == 0:
            custom_colors = cols1[:-1] + col_mid + cols2[1:]
    elif custb == 4:
        max_range = None            
        custom_bounds = []
        numinputs = 8 #how many to try and read
        for i in range(1, numinputs + 1):
            nb = request.form.get(f'inputbn{i}4', 2020).strip()
            pb = request.form.get(f'inputbp{i}4', 2020).strip()
            if nb == 2020 or nb == '':
                break
            nb = float(nb)
            pb = float(pb)
            custom_bounds.extend([nb, pb])
            if zerobound == 1:
                custom_bounds.append(0)
        numinputs = len(custom_bounds) // 2
        if zerobound == 1:
            numinputs == numinputs + 1
        numbshades = numinputs-1
        colorchoicetype = float(request.form['optionc'])
        if colorchoicetype == 1:
            negshadein = str(request.form['negcolorid']).strip()
            posshadein = str(request.form['poscolorid']).strip()
            c1 = negshadein
            c2 = '#FFFFFF'
            c3 = posshadein
            col_mid = [mc.to_hex(c2)]
            if zerobound == 1:
                cols1 = [colorFader(c1,c2,x/numbshades) for x in range(numbshades)]
                cols2 = [colorFader(c2,c3,x/numbshades) for x in range(numbshades)]
                custom_colors = cols1[:-1] +cols2[1:]
            if zerobound == 0:
                cols1 = [colorFader(c1,c2,x/numbshades) for x in range(numbshades+1)]
                cols2 = [colorFader(c2,c3,x/numbshades) for x in range(numbshades+1)]
                custom_colors = cols1[:-1] + col_mid + cols2[1:]
        elif colorchoicetype ==2: 
            custom_colors = []
            nc_list = []
            pc_list = []
            col_mid = mc.to_rgb('#FFFFFF')  # assuming mc is matplotlib.colors
            for i in range(1, numinputs):
                nc = request.form.get(f'ninputcol{i}', 2020).strip()
                pc = request.form.get(f'pinputcol{i}', 2020).strip()
                if nc == 2020 or nc == '':
                    break
                nc_list.append(mc.to_rgb(nc))
                pc_list.append(mc.to_rgb(pc))
            for nc in nc_list:
                custom_colors.append(nc)
            if zerobound == 0:
                custom_colors.append(col_mid)
            for pc in pc_list:
                custom_colors.append(pc)

    #Determine if Advanced Options were chosen, if yes import those values
    dtime = int(request.form.get('droptime', 0))
    dpept = int(request.form.get('droppept', 0))
    dprot = int(request.form.get('dropprot', 0))
    renumdict = int(request.form.get('renumdict', 0))
    iddict = int(request.form.get('mutiddict', 0))
    mutdict = int(request.form.get('mutdict', 0))
    slist = int(request.form.get('statelist', 0))
    if renumdict == 1:
        key1 = str(request.form['key1']).strip()
        value1 = (request.form['value1'])
        key2 = str(request.form['key2']).strip()
        value2 = (request.form['value2'])
        # Constructing the variable, currently can do 2 proteins, should improve
        if key2 == '':
            renumbering_dict = {key1: value1}
        else:
            renumbering_dict = {key1: value1, key2: value2}
    if iddict == 1:
        mutidWT = str(request.form['wtpro1']).strip()
        mutidMUT = str(request.form['mutpro1']).strip()
        mut_id_dict = {mutidMUT : mutidWT} 
    if mutdict == 1:
        mutdictres = float(request.form['mutdictres'])
        mutdictwt = request.form['mutdictwt'].strip()
        mutation_dict = {mutdictres : mutdictwt}
    if dtime == 1:
        num_timedao = int(request.form.get('numtimedao', 7))
        drop_times = [request.form[f'dt{i}'] for i in range(1, num_timedao) if request.form[f'dt{i}']]
    if dpept == 1:
        drop_pept = []
        num_dpept = int(request.form.get('numpeptd', 4))
        for i in range(1, num_dpept):
            dpeppro = request.form.get(f'dpeppro{i}', '')
            dpepst = float(request.form.get(f'dpepst{i}', 0))
            dpepend = float(request.form.get(f'dpepend{i}', 0))
            if dpeppro:
                drop_pept.append((dpeppro, dpepst, dpepend))
    if dprot == 1:
        drop_prot = []
        for i in range(1, 7):
            dpro = request.form.get(f'dpro{i}', '')
            if dpro:
                drop_prot.append(dpro)
            else:
                break
    if slist == 1:
        state1_list = []
        state2_list = []
        for i in range(1, 7):
            s1 = request.form.get(f's1{i}', '')
            s2 = request.form.get(f's2{i}', '')
            if s1 != '':
                state1_list.append(s1)
                if s2 == '':
                    s2 = request.form.get('s21', '')  # Default to s21 if s2 is empty
            state2_list.append(s2)
        # Ensure that state1_list and state2_list have the same length
        state1_list = state1_list[:len(state2_list)]
    
    buffer = BytesIO()  # saves plot to BytesIO buffer
    
    output_csv_file  = r'HDX processed data.csv'
    output_pdf_file  = r'C:\\Users\\kentv\\heatmap\\uploads\\HDX heatmap.pdf'
    
    # File name, format, and resolution for a bitmap image output of heatmap plots.
    # By default the script saves all plots into one combined pdf and individual bitmap files. Set output_bitmap = 0 if saved bitmaps are not needed.
    # Plot files have names in the following style: name_x_N.format
    # where x is either 'h' or 'v' and N is an integer starting at 0 and automatically incremented for each plot.
    # Format must be one of the formats that matplotlib.pyplot.savefig() understands, e.g. 'png', 'jpg', 'tiff';
    # (format can also be a vector graphics format such as 'pdf' or 'svg')
    
    output_bitmap = 1
    output_bitmap_name = 'HDX heatmap'
    output_bitmap_dpi = 100
    dif_dpi = float(request.form.get('dif_dpi', 0))
    print(dif_dpi)
    print('this is if difdpi is working')
    if dif_dpi != 0:
        output_bitmap_dpi = float(request.form.get('dpi_in'))
    print(output_bitmap_dpi)
    if PDFgeneration == 1:
        output_bitmap_format = 'pdf'
    else:
        output_bitmap_format = 'png'
    
    # By default, when altering mutant peptide sequence and protein ID, script prints one-line message for each row processed.
    # If this is unwanted, set mutation_msg=0
    
    mutation_msg = 0
    
 
    # --------------------------------------------------------------------------------------------------------
    
    # Optional parameters to filter only significant data based on p-values, and to produce p-value scatter plots.
    
    # The script attemps calculating means and standard deviations for each D exposure time for each state based on any number
    # of replicates present in the data. It then computes D uptake differences between different protein states/conditions
    # and calculates p-values for each difference. If there are no replicates in the data (i.e. only a single measurement at each time)
    # p-values are undetermined. Data is not filtered if there are no replicates.
    # If replicates are present at least for some of data, by default the script applies p-value filtration to the data before it is plotted
    # in the heatmap (and before pymol macros are generated): all insignificant D uptake differences are set to zero.
    # The user can change p-value threshold for filtering the data, variable 'p_threshold'
    # The user can elect to avoid any p-value filtration by setting variable 'significant_only' to zero.
    # The user may also elect to produce volcano plots of p-value vs. D uptake difference. By default the script does not produce these plots.
    # Location for saving the volcano plots is set by variable 'scatter_dir', which be default is subdirectory 'scatter_plots'
    
    # --------------------------------------------------------------------------------------------------------
    # Optional variables to control splitting of heatmap plots into smaller segments.
    # Due to the nature of HDX data, heatmap plots tend to be extremely elongated rectangles, summarizing a few HDX time points across many peptides.
    # Frequently it is Aesthetically Pleasing™ to break down such elongated plots into a few fragments which are less elongated. This script can split the plot into
    # pieces by 3 criteria: by protein; into a defined number of pieces of same size; into an arbitrary number of pieces of arbitrary size, set by the user.
    
    # Splitting by protein is done by setting variable split_outp_by_prot. By default it is set to an empty string, which means no splitting.
    # If split_outp_by_prot = 'all' then data from each protein ID will be drawn in its own plot;
    # If split_outp_by_prot is set to a list of protein IDs, then the script will draw data from these IDs into separate plots.
    # If protein IDs in the split_outp_by_prot list are enclosed by parentheses to make a python tuple, data from these protein IDs is combined into a single plot.
    # Also, if the split_outp_by_prot is set to a list, then any protein IDs in the data but not in the list will be omitted from plotting. 
    # This is similar to using drop_prot variable as explained above.
    # Example. Let's say input data contains 4 protein IDs in the 'Protein' column of the input csv: A, B, C, D. Then:
    # 1) split_outp_by_prot = '' (default) and drop_prot = [] (default) creates a single plot with all 4 protein IDs in that plot.
    # 2) split_outp_by_prot = '' and drop_prot = ['B', 'D'] creates a single plot with data from proteins A and C in it.
    # 3) split_outp_by_prot = 'all' creates 4 plots - one for each protein.
    # 4) split_outp_by_prot = ['A', 'B', 'C', 'D']  - same as #3.
    # 5) split_outp_by_prot = [('A', 'B'), 'C', 'D']  - creates 3 plots; 1 containing proteins A and B, next containing protein C, 3rd containing D.
    # 6) split_outp_by_prot = ['A', 'C'] - creates 2 plots; 1 containing protein A data, the other containing protein C data. B and D are not plotted.
    # 7) split_outp_by_prot = [('A', 'C')] - same shape of output as #2, data from A and C in a single plot. However, in some cases the colors might be different from the case where
    # drop_prot = ['B', 'D'] is used, as explained in the drop_prot variable section.
    # Protein IDs in the split_outp_by_prot must match those in the input data. Using an unrecognized protein ID will raise KeyError.
    # Splitting into smaller segments for plotting is applied to the data after dropping (if any), thus the above caveat applies
    # even when data corresponding to a protein ID was present in the input but was removed from a final data frame during processing
    # by setting the drop_prot variable, or the script auto-dropped that protein ID because all of the D uptake differences computed for that ID are empty.
    
    # Variable split_outp_chunks, if set to a non-zero integer N, causes the the plot to be split into N segments of same size (within 1 peptide).
    # Variable split_outp_by_row, if set to a list containing integers, causes the the plot to be split into segments at the row numbers indicated in the list.
    # This is the most flexible splitting option and can be used to divide the plots into arbitrary segments.
    # Example: split_outp_by_row = [60, 100] breaks output heatmaps into 3 pieces: first 60 peptides from the input (i.e. top 60 rows in the final processed dataframe) into one plot,
    # then next 40 peptides into another plot, and all the remaining peptides into the 3rd plot.
    
    # Which option for heatmap splitting is applied is decided based on variable settings, in the following increasing priority:
    # split_outp_by_prot = '' (or []), split_outp_chunks = 0, split_outp_by_row = [] - default values, no splitting, lowest priority
    # split_outp_by_row = list of integers; to use this keep split_outp_by_prot = '' and split_outp_chunks = 0
    # split_outp_chunks = integer; to use this keep split_outp_by_prot = '' 
    # split_outp_by_prot = list of protein IDs
    # if split_outp_by_prot is set to a string which is not empty and not 'all', the script will complain and produce no output plots
    # split_outp_by_prot = 'all' highest priority
    
    # Splitting of heatmap plots into pieces has no effect on pymol macro output.
    
    split_outp_by_prot = 'all'
    # split_outp_by_prot = ['PSA_MYCTU', ('PSB_MYCTU', 'PSB_T1A')]
    # split_outp_by_prot = ['PSB_MYCTU']
    # split_outp_chunks = 2
    # split_outp_by_row = [60, 100]

    # --------------------------------------------------------------------------------------------------------
    
    # Plot heatmaps of all states stacked into a single figure or each state into a separate figure, or both?
    # Be default only separate plots are produced. If stacked plots are desired set plot_stacked = 1
    # Set plot_separate = 0 to avoid plotting separate figures
    
    plot_stacked  = 1
    plot_separate = 0
    
    # --------------------------------------------------------------------------------------------------------
    
    #Plot here:
    if custom_colors != None and custom_bounds != None:
        custom_bounds = list(set(custom_bounds))
        print(len(custom_colors))
        print(custom_colors)
        print(custom_bounds)
        print(len(custom_bounds))
        if len(custom_colors)>=1 and len(custom_bounds)>=1 and (len(custom_bounds) != len(custom_colors)+1):
            print('It appears that both custom_colors and custom_bounds lists are used together, but there is mismatch between expected numbers of entries.')
            print('custom_bounds list must have exactly one more entry than custom_colors. Aborting processing.')
            raise StopExecution
    if custom_colors != None and custom_bounds != None:
        if len(custom_colors)==0 and len(custom_bounds)==1:
            print('custom_bounds list must contain two or more numbers. Aborting processing.')
            raise StopExecution
    if custom_bounds != None:
        custom_bounds.sort()
    
    if (not plot_h) and (not plot_v) and (not plot_w):
        print('Both variables \'plot_h\' and \'plot_v\' are set to zero. No heatmap plots will be produced.\n')
    if (not plot_stacked) and (not plot_separate):
        print('Both variables \'plot_stacked\' and \'plot_separate\' are set to zero. No heatmap plots will be produced.\n')
    
    # Read the input and start processing:
    data_df = pd.read_csv(input_csv_file)
    
    if 'z' not in data_df.columns:
        print('No charge data (\'z\' column) in the input file. Assuming z=1 for all peptides.')
        print('Your D uptake values will be severely underestimated if actually z>1.\n')
        data_df['z'] = 1
    
    # Renumber residues, if desired:
    if renumbering_dict != None:
        if len(renumbering_dict)>0:
            print('Renumbering residues of protein IDs specified in renumbering_dict.\n')
            for prot, shift in renumbering_dict.items():
                shift = pd.to_numeric(shift, errors='coerce')
                data_df.loc[data_df['Protein'] == prot, ['Start', 'End']] -= shift
                #data_df.loc[ data_df['Protein']==prot, ['Start','End'] ] = data_df.loc[ data_df['Protein']==prot, ['Start','End'] ] - shift
        
    # Mutate protein, if desired (i.e. change 'Protein' and 'Sequence' for peptides in proteins specified in mut_id_dict)
    if mutation_dict != None and mut_id_dict != None:
        if len(mutation_dict)>0 and len(mut_id_dict)==0:
            print("A list of residue mutations is provided in mutation_dict, but dictionary mut_id_dict is empty, thus it is impossible to know which protein IDs should be altered. No mutation will be applied.\n")
    
    if mut_id_dict != None:    
        if len(mut_id_dict)>0:
            data_df['Original'] = 1
            for mut_id, wt_id in mut_id_dict.items():
                mut_indices = data_df.loc[ data_df['Protein']==mut_id ].index
                print("Attempting to change data entries of mutant protein '%s' to have protein IDs and peptide sequences same as wild type protein '%s'." % (mut_id, wt_id))
                if len(mutation_dict)>0:
                    print("Using list of mutations provided by the user in mutation_dic.\n")
                else:
                    print("No mutation list is provided in mutation_dict. Will look up wt peptide sequences from non-mutant protein state(s).\n")
                    mut2wt_df = data_df.loc[data_df['Protein']==wt_id , ['Start','End','Sequence']].groupby(['Start','End']).first()
                for idx in mut_indices:
                    mut_start = data_df.loc[idx , 'Start']
                    mut_end   = data_df.loc[idx , 'End']
                    mut_state = data_df.loc[idx , 'State']
                    mut_seq   = data_df.loc[idx , 'Sequence']
                    # Count number of rows containing same peptide with the same 'State' string from the wt protein, abort execution if it's more than zero
                    seq_exist = data_df.loc[ (data_df['Protein']==wt_id) & (data_df['Start']==mut_start) & (data_df['End']==mut_end) & (data_df['State']==mut_state) & data_df['Original'] ].shape[0]
                    if seq_exist:
                        print("Input data table row %d contains an entry for a peptide from mutant protein which should be turned into a wt peptide/protein:\n" % idx)
                        print(data_df.loc[idx].to_frame().T)
                        print("\nHowever, wt protein already contains that peptide with an identical 'State' label.\nTurning mutant into a wt peptide for the same state would create erroneous data for this peptide/state combo.\nLikely mutant protein data is labeled with a wrong 'State' in the input csv. Aborting processing.\n")
                        raise StopExecution
                    if len(mutation_dict)>0:
                        for res, aa in mutation_dict.items():
                            if mut_start<=res and mut_end>=res:
                                if mut_seq[res-mut_start]==aa:
                                    print("mutation_dict specifies that residue #%d should be turned into %s. However, it already is %s. Aborting processing.\n" % (res, aa, aa))
                                    raise StopExecution
                                wt_seq = mut_seq[:res-mut_start] + aa + mut_seq[res-mut_start+1:]
                    else:
                        # This used to run fine on an older version of Pandas:
                        # wt_seq    = mut2wt_df.loc[ (mut_start, mut_end) ][0]
                        # But now it produces a warning FutureWarning: Series.__getitem__ treating keys as positions is deprecated. In a future version, integer keys will always be treated as labels
                        # Apparently we are no longer allowed to access n-th element of series by doing 'series[n-1]', our coding experience has been much improved by forcing us to use 'series.iloc[n-1]'
                        wt_seq    = mut2wt_df.loc[ (mut_start, mut_end) ].iloc[0]
                    if mutation_msg:
                        print("Input row %d, changing protein %s peptide %d-%d %s state %s to %s %s" % (idx, mut_id, mut_start, mut_end, mut_seq, mut_state, wt_id, wt_seq))
                    data_df.loc[idx , 'Protein'] = wt_id
                    data_df.loc[idx , 'Sequence'] = wt_seq
                    data_df.loc[idx , 'Original'] = 0
                print('')
    
    # Start d_uptake calculations.
    # Decharge:
    data_df['Center'] = (data_df['Center']-mp) * data_df['z']
    
    # Compute average and std.dev. values for replicates at each time point. This includes replicates of no D exposure samples, if present in the data:
    data_avg = data_df.groupby(['Protein', 'Start', 'End', 'Sequence', 'State', 'Exposure']).agg({'Center': ['mean', 'std','count']})

    # Reshape the dataframe so that each column represents one D exposure time.
    # Then subtract time=0 column for each state from time !=0 columns to get D uptake values at each time:
    
    data_avg = data_avg.unstack('Exposure')
    data_avg.loc[:,('Center','mean',slice(None))] = data_avg.loc[:,('Center','mean',slice(None))].sub( data_avg['Center','mean',0], axis=0 )
    data_avg.loc[:,('Center','std',slice(None))]  = data_avg.loc[:,('Center','std',slice(None))].add( data_avg['Center','std',0].fillna(0), axis=0 )
    data_avg.columns=data_avg.columns.set_levels(['d_uptake'],level=0)
    data_avg.columns=data_avg.columns.rename('Parameter', level=1)
    
    # Drop no longer needed columns with time=0:
    data_avg = data_avg.drop(columns=0, level='Exposure')
    
    # We could keep working with the df in its current shape, but if we transform 'State' from row into column labels,
    # it could be marginally easier to make correct .loc[] selection for subsequent subtractions.
    # Merely applying .unstack('State') creates the order of column labels that is not aesthetically pleasing, thus let's stack
    # 'Exposure' first, then unstack both 'State' and 'Exposure' in that order:
    data_avg=data_avg.stack('Exposure').unstack(level=['State','Exposure'])
    
  
    
    # Make a list of states for D uptake difference calculation:
    all_states = data_avg.columns.get_level_values('State').unique()
    if len(all_states) == 1:
        print('There is only 1 state in the input csv file: \'%s\'' % all_states[0])
        print('Need 2 or more states to calculate D uptake difference.\n')
        raise StopExecution
    if state1_list != None and state2_list != None:
        if len(state1_list) != len(state2_list):
            print('state1_list and state2_list (the lists of protein states for difference calculation) have unequal lengths.')
            print('If this is not intentional, there may be some D uptake difference calculations missing from the output.\n')
        state_list = list(zip(state1_list, state2_list))
    
    if not state_list:
        state_list=list(itertools.combinations(all_states,2))
        print('A list of protein states for D uptake difference calculation was not provided.')
        print('There are total of %d states in the input csv file.' % len(all_states))
        print('Will calculate all-against-all D uptake differeces, total of %d comparisons.\n' % len(state_list))
    
    # Calculate D uptake differences between states. Append data to data_avg:
    diffs = pd.DataFrame()
    for two_states in state_list:
        state1 = two_states[0]
        state2 = two_states[1]
        if state1 == state2:
            print('Found a request to calculate difference between a state \'%s\' and itself.' % state1)
            print('There may be a typo, or the orders of states might be mixed up, in the \'state1_list\' or \'state2_list\'.\n')
        mean = data_avg.loc[:,('d_uptake','mean',state1,slice(None))] - data_avg.loc[:,('d_uptake','mean',state2,slice(None))].values
        std  = data_avg.loc[:,('d_uptake','std',state1,slice(None))]  + data_avg.loc[:,('d_uptake','std',state2,slice(None))].values
        pval = ttest_ind_from_stats( data_avg.loc[:,('d_uptake','mean',state1,slice(None))], data_avg.loc[:,('d_uptake','std',state1,slice(None))], data_avg.loc[:,('d_uptake','count',state1,slice(None))], data_avg.loc[:,('d_uptake','mean',state2,slice(None))].values, data_avg.loc[:,('d_uptake','std',state2,slice(None))].values, data_avg.loc[:,('d_uptake','count',state2,slice(None))].values, equal_var=False)[1]
        pval = pval.rename(columns={'count': 'pval'}, level='Parameter')
        # Right now columns are labeled with state1 at 'State' level.
        # We want names of both state1 and state2 in there
        new_state = state1 + ' - ' + state2
        d = {state1 : new_state}
        mean = mean.rename(columns=d, level='State')
        std  = std.rename(columns=d, level='State')
        pval = pval.rename(columns=d, level='State')
        diffs = pd.concat([diffs, mean, std, pval], axis=1)
    
    # In an older version of Pandas it used to be possible to run the next line inside the 'for' loop above and then concatenate result to 'data_avg' before going to the next iteration of 'for'.
    # diffs.columns=diffs.columns.set_levels(['Delta_d_uptake'],level=0)
    # The only thing this line does, it takes all existing labels at level 0 (all of them are 'd_uptake') and renames them to 'Delta_d_uptake'.
    # At some point a new property was added to pandas multiindex, 'codes'. Which may be convenient in some cases. But now there is a requirement
    # that levels list and codes list must be consistent. So that line of code works on a 1st pass of the loop, since at that time there is only
    # 'd_uptake'. But on 2nd pass it crashes, b/c now you are trying to set_levels using a list of len=1, while the list of codes has len=2
    # I have not tested, perhaps it still is possible to use it with the keyword verify_integrity=False.
    # It also should be possible to use .set_codes() to accomplish same result, but seems like more work.
    # My solution is to delay appending 'diffs' to 'data_avg' - I'm no longer doing that inside the 'for' loop.
    # I'm doing it after all mean and std. dev. have been computed and collected into 'diffs', then rename
    # 'd_uptake' to 'Delta_d_uptake' once, and concatenate it to 'data_avg'. Arguably, concatenating 'diffs' to 'data_avg' is unnecessary, since I extract that data into
    # 'all_deltas' soon afterwards. But at one point I liked having all processed data in a single df.
    
    diffs.columns=diffs.columns.set_levels(['Delta_d_uptake'],level=0)
    data_avg=pd.concat([data_avg, diffs], axis=1)
    
    # All calculations complete. Save the data to csv:
    try:
        data_avg.to_csv(output_csv_file)
        print("Processed data was written into a csv file '%s'\n" % output_csv_file)
    except IOError:
        curr_time = time.localtime()
        time_string = "%s.%s.%s_%s.%s.%s" % (curr_time[:6])
        new_output_csv_file = output_csv_file + "_" + time_string + "_.csv"
        data_avg.to_csv(new_output_csv_file)
        print("Could not write csv output into file '%s'" % output_csv_file)
        print("On Windows this often happens when file already exists and is open.")
        print("Your csv output was written into a file with a new file name containing an appended unique date and time string.")
        print("Date and time string is in the format of: year.month.day_hour.minute.second")
        print("New file name is '%s'\n" % new_output_csv_file)

    # Drop time points unwanted by the user, individual peptides unwanted by the user, and entire proteins unwanted by the user:
    if drop_times != None:
        data_avg = data_avg.drop(columns=drop_times, level='Exposure')
    if drop_pept != None:
        data_avg = data_avg.drop(index=drop_pept)
    if drop_prot != None:    
        data_avg = data_avg.drop(index=drop_prot)
    
    # Start plotting by grabbing Delta_d_uptake from data_avg and finding the maximal difference
    # in D uptake in the entire data set. This maximum will define the color range,
    # unless user specified otherwise by setting the max_range variable or custom_bounds list:
    all_deltas = data_avg.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
    max_delta_pos = all_deltas.max().max()  # axis=None does not work in older versions of pandas
    max_delta_neg = all_deltas.min().min()
    max_delta = max([abs(max_delta_pos), abs(max_delta_neg)])   
    if custb == 2:
        max_range = round(max_delta, 1)

    # A function to create bounds list for heatmap color bins. Output will be passed into matplotlib.colors.BoundaryNorm()
    def make_bounds(tot_colors, max_delta=max_delta):
        custb = float(request.form['option'])
        zerobound = float(request.form.get('zerobound', 0))
        if custb ==3:
            max_range = float(request.form['max_range'])
            max_range = round(max_range, 1)
        if custb ==2:
            max_range = round(max_delta, 1)
        num_shades = np.ceil(tot_colors / 2).astype(int)   # larger by 1 for odd tot_colors  
        num_shades = round(num_shades)
        if max_range:
            incr = max_range / num_shades
        else:
            incr = np.ceil(10 * max_delta / num_shades)/10
            max_range = incr * num_shades
        if tot_colors % 2 == 0:
            bounds = np.linspace(-max_range, max_range, num = tot_colors+1)
            if zerobound == 1:
                bounds = np.linspace(-max_range, max_range, num = tot_colors)
                bounds = np.append(bounds, 0)
        else:
            half = np.linspace(incr, max_range, num = num_shades)
            if zerobound == 0:
                bounds = np.append(-half, half)
            elif zerobound == 1:
                bounds = np.append(-half, half)
                bounds = np.append(bounds, 0)
            bounds = np.sort(bounds)
        if zerobound == 1:
            bounds = np.append(bounds, 0)
            bounds = list(set(bounds))
            bounds = np.sort(bounds)
        return bounds

    print("Maximal difference in D uptake between protein states in the data is %.2f." % max_delta)
    if max_range != None:
        if max_range:
            print("The user has set max_range=%.2f; using this value for the color scale instead of above maximal difference." % max_range)
    print('')
    
    # Drop columns and rows that are completely empty in all_deltas:
    old_shape = all_deltas.shape
    all_deltas = all_deltas.dropna(axis=0, how='all') # rows
    all_deltas = all_deltas.dropna(axis=1, how='all') # columns
    if all_deltas.shape[0] < old_shape[0]:
        print('Before plotting, removed %d rows from D uptake difference table that are completely empty. This happens when\nsome peptides are present in only one of the protein states.\nYou may wish to inspect output csv file to make sure processed data looks reasonable.\n' % (old_shape[0] - all_deltas.shape[0]))
    if all_deltas.shape[1] < old_shape[1]:
        print('Before plotting, removed %d columns from D uptake difference table that are completely empty. This happens when\nsome time points are present in only one of the protein states.\nYou may wish to inspect output csv file to make sure processed data looks reasonable.\n' % (old_shape[1] - all_deltas.shape[1]))
    all_pvals           = data_avg.loc[:,('Delta_d_uptake','pval',slice(None),slice(None))]        # after per forming .dropna() on all_deltas, potentially there are more columns in all_pvals than in all_deltas
    columns_of_interest = all_deltas.rename(columns={'mean': 'pval'}, level='Parameter').columns   # columns from all_deltas, renamed to look like from all_pvals
    all_pvals           = all_pvals.loc[:, columns_of_interest]                                    # now same columns are in all_pvals as in all_deltas
    all_pvals           = all_pvals.loc[all_deltas.index, :]                                       # same for rows
    
    # Make p-value vs. D uptake difference volcano plots: create a directory; then loop through all states and times to plot data
    all_states = all_deltas.columns.get_level_values('State').unique()
    
    ######SCATTER PLOTTING#######
    scatter_plot = request.form.get('scatterplot', 2020)
    if scatter_plot != 2020:
        scatter_plot = float(scatter_plot)
    p_threshold = request.form.get('pthresh', 0.05)
    if p_threshold == '':
        p_threshold = 0.05
    if p_threshold != 0.05 and p_threshold != '':
        p_threshold = float(p_threshold)
    if scatter_plot != 2020:
        if scatter_dir:
            Path(scatter_dir).mkdir(parents=True, exist_ok=True)
        scatter_buffer = io.BytesIO()  # Create an in-memory zip file buffer
        with zipfile.ZipFile(scatter_buffer, 'a', zipfile.ZIP_DEFLATED, False) as zip_file:
            for state in all_states:
                all_times = all_deltas.loc[:, ('Delta_d_uptake', 'mean', state, slice(None))].columns.get_level_values('Exposure').unique()
                for i in all_times:
                    title = '%s, exposure: %s' % (state, str(i))
                    fig = plt.figure(figsize=(12, 10))
                    plt.plot(all_deltas.loc[:, ('Delta_d_uptake', 'mean', state, i)], -all_pvals.loc[:, ('Delta_d_uptake', 'pval', state, i)].map(np.log10), 'ko')
                    plt.axhline(y=-np.log10(p_threshold), color='k', linewidth=1)
                    plt.axvline(x=-Dd_threshold, color='k', linewidth=1)
                    plt.axvline(x=Dd_threshold, color='k', linewidth=1)
                    plt.title(title)
                    plt.ylabel('-log$_{10}$(p-value)')
                    plt.xlabel('Δ(D uptake), Da')
                    plt.xlim([-max_delta * 1.05, max_delta * 1.05])
                    file_name = "volcano_plot_%s_%s.%s" % (state, str(i), output_bitmap_format)
                    plt.savefig(file_name, dpi=output_bitmap_dpi)
                    plt.close()
                    if scatter_dir:
                        file_path = scatter_dir + "/" + file_name
                    else:
                        file_path = file_name
                    zip_file.write(file_name)  # Add the file to the zip archive
                    # Remove the file after adding it to the zip archive
                    Path(file_name).unlink()
        # Save the zip buffer to a file or return it as a response in Flask, depending on your use case
        with open('scatter_plots.zip', 'wb') as f:
            f.write(scatter_buffer.getvalue())
    
    # Data filtration based on p-values:
    if significant_only:
        count_pvals = all_pvals.notna().sum()
        no_reps_bool = (count_pvals==0)
        no_reps_tot  = no_reps_bool.sum()
        all_pvals_bool = (all_pvals>p_threshold)
        all_deltas = all_deltas.mask(all_pvals_bool.values, 0)
        if no_reps_tot == len(count_pvals):   # all data is missing replicates
            print('None of %d protein states and exposure time combinations appear to contain replicated data. No P-value filtering will be applied.\n' % no_reps_tot)
        else:
            if no_reps_tot > 0:   # looks like some, but not all data has missing replicates
                print('%d of %d protein states and exposure time combinations do not have replicated data. P-value filtering is not applied to this data.\n' % no_reps_tot, len(count_pvals))
            print('Set %d D uptake differences with larger than %.2e p-values to 0 before plotting the data.\n' % (all_pvals_bool.sum().sum(), p_threshold))
    
    #Setup colormap color list and bin boundaries:
    if custom_colors != None:
        if custom_colors:
            colors = custom_colors
            if custom_bounds != None:
                if custom_bounds:
                    bounds = custom_bounds
                    print('bounds and ccol')
            else:
                bounds = make_bounds(len(colors))
                print('no bounds found')
    elif custom_bounds != None:
        if custom_bounds:
            print("The user has provided custom_bounds list and no custom_colors list. Using custom_bounds to calculate colors, and ingnoring max_range and num_shades variables.\n")
            b = np.array(custom_bounds)
            # the 3 variables below assume there is a zero value in the custom_bounds list, which divides all data into positive colors and negative colors:
            neg_shades = len(b[b<0])
            pos_shades = len(b[b>0])
            col_mid = []
            # if zero is absent from the custom_bounds list, then set the middle color to c2 (default white), but only if custom_bounds list has at least one value on each side of zero!
            # Also, decrease number of shades on each side of zero by one:
            if len(b[b==0])==0:
                if neg_shades>0 and pos_shades>0:
                    col_mid = [ mc.to_hex(c2) ]
                    if zerobound == 0:
                        neg_shades = len(b[b<0])-1
                        pos_shades = len(b[b>0])-1
                    if zerobound == 1:
                        neg_shades = len(b[b<0])
                        pos_shades = len(b[b>0])
            if neg_shades > 0:
                cols1 = [colorFader(c1,c2,x/neg_shades) for x in range(neg_shades+1)]
            else:
                cols1 = [ mc.to_hex(c2) ]
            if pos_shades>0:
                cols2 = [colorFader(c2,c3,x/pos_shades) for x in range(pos_shades+1)]
            else:
                cols2 = [ mc.to_hex(c2) ]
            if zerobound == 0:
                colors = cols1[:-1] + col_mid + cols2[1:]
            if zerobound == 1:
                colors = cols1[:-1] + cols2[1:]
            bounds = custom_bounds
            print(bounds)
            print('no ccol')
    else:
        # c_missing is color to use in the heatmap for the missing data in the input file.
        # c_missing is used regardless whether the user provided a color map or not.
        c_missing = '#bdbdbd' # gray;
        num_shades = round(num_shades) # Convert num_shades to integer if it's a float
        if zerobound == 0:
            cols1 = [colorFader(c1,c2,x/num_shades) for x in range(num_shades+1)]
            cols2 = [colorFader(c2,c3,x/num_shades) for x in range(num_shades+1)]
            colors = cols1 + cols2[1:]
        if zerobound == 1:
            cols1 = [colorFader(c1, c2, (x/num_shades)) for x in range(num_shades+1)]
            cols2 = [colorFader(c2, c3, (x/num_shades)) for x in range(num_shades+1)]
            colors = cols1[:-1] + cols2[1:]
        print
        bounds = make_bounds(len(colors))
        if zerobound == 1:
            bounds = np.append(bounds, 0)
            bounds = list(set(bounds))
            bounds = np.sort(bounds)
        print(bounds)
        print('no ccol or bounds found')

    colormap = mc.ListedColormap(colors)
    print(colors)
    print(bounds)
    print('right before calling')
    my_norm = mc.BoundaryNorm(bounds, ncolors=len(colors))

    all_deltas.reset_index(level=['Protein','Start','End'],inplace=True)
        
    # Open pdf output file:
    pdf=PdfPages(output_pdf_file)  # This used to throw IOError if file is write-protected, but no longer does so.
    try:
        pdf.attach_note('')        # To test if file is write-protected, try adding a comment (empty string).
    except IOError:
        curr_time = time.localtime()
        time_string = "%s.%s.%s_%s.%s.%s" % (curr_time[:6])
        new_output_pdf_file = output_pdf_file + "_" + time_string + "_.pdf"
        pdf=PdfPages(new_output_pdf_file)
        print("Could not write pdf output into file '%s'" % output_pdf_file)
        print("On Windows this often happens when file already exists and is open.")
        print("Your pdf output was written into a file with a new file name containing an appended unique date and time string.")
        print("Date and time string is in the format of: year.month.day_hour.minute.second")
        print("New file name is '%s'\n" % new_output_pdf_file)
    plt.rcParams['font.size'] = font_size
    
    def make_time_tick_labels(time_list):
        labels = []
        for hdx_time in time_list:
            if hdx_time < 1:
                string = '%s s' % np.round(hdx_time*60).astype(int)
            elif hdx_time < 60:
                mins = np.floor(hdx_time).astype(int)
                sec = np.round(np.remainder(hdx_time, 1)*60).astype(int)
                if sec > 0:
                    string = '%s m %s s' % (mins, sec)
                else:
                    string = '%s m' % mins
            else:
                hour = np.round(hdx_time/60).astype(int)
                mins  = np.round(np.remainder(hdx_time, 60)).astype(int)
                if mins > 0:
                    string = '%s h %s m' % (hour, mins)
                else:
                    string = '%s h' % hour
            labels.append(string)
        return(labels)
    
    # Iterate through the list of computed D uptake differences and plot them:
    def h_plot(pdf,data,title,pept):
        global output_bitmap_h_count
        fig_margin_x_l = 3
        fig_margin_x_r = 1
        fig_margin_y_t = 4
        fig_margin_y_b = 3
        fig_length_x = data.shape[0]
        fig_length_y = data.shape[1]
        fig_x = fig_margin_x_l + fig_length_x + fig_margin_x_r
        fig_y = fig_margin_y_b + fig_length_y + fig_margin_y_t
        cbar_spacer = 0.5  # Gap between heatmap plot and colorbar
        cbar_length  = min(len(colors), fig_length_x)  # 10 or fig_length_x, whichever is smaller
        # make tick labels:
        pept_tick_labels = pept['Start'].map(str) + '-' + pept['End'].map(str)
        time_tick_labels = make_time_tick_labels( data.columns.get_level_values('Exposure') )
        fig = plt.figure(figsize=(fig_x , fig_y), dpi=output_bitmap_dpi)
        ax = plt.axes((fig_margin_x_l/fig_x, fig_margin_y_b/fig_y, fig_length_x/fig_x, fig_length_y/fig_y ))
        ax_4_cbar = plt.axes(( (fig_margin_x_l+(fig_length_x-cbar_length)/2)/fig_x, (fig_margin_y_b - cbar_spacer - cbar_length/len(colors))/fig_y, cbar_length/fig_x, cbar_length/len(colors)/fig_y ))
        sns.heatmap(data.transpose(), ax=ax, cmap=colormap, norm=my_norm, xticklabels=pept_tick_labels, yticklabels=time_tick_labels, linewidths=0.30, square=True, cbar_ax=ax_4_cbar, cbar_kws={"orientation": "horizontal"})
        plt.sca(ax)
        ax.set_facecolor(c_missing)
        plt.title(title,fontsize=font_size_title)
        plt.ylabel('H/D exchange time')
        plt.xlabel('Peptides')
        ax.xaxis.tick_top()
        ax.xaxis.set_label_position('top')
        ax.tick_params(axis = 'x', labelrotation = 90)
        ax.tick_params(axis = 'y', labelrotation = 0)
        #Placing black line around the plot:
        ax.axhline(y=0, color='k',linewidth=10)
        ax.axhline(y=fig_length_y, color='k',linewidth=10)
        ax.axvline(x=0, color='k',linewidth=10)
        ax.axvline(x=fig_length_x, color='k',linewidth=10)
        # Add separator lines between states:
        states = data.columns.get_level_values('State').unique()
        sep_line_y = 0
        for i in range(len(states)-1):
            exposures = data.loc[:,('Delta_d_uptake','mean',states[i],slice(None))].columns.get_level_values('Exposure')
            sep_line_y += len(exposures)
            ax.axhline(y=sep_line_y, color='k',linewidth=5)
        pdf.savefig()  # saves the current figure into a pdf page
        if output_bitmap:
            output_bitmap_file = output_bitmap_name + '_h_' + str(output_bitmap_h_count) + '.' + output_bitmap_format
            plt.savefig(output_bitmap_file, dpi=output_bitmap_dpi)
            output_bitmap_h_count += 1
        if PDFgeneration == 1:
            plt.savefig(buffer, format='pdf', dpi=output_bitmap_dpi)
        else:
            plt.savefig(buffer, format='png', dpi=output_bitmap_dpi)
        buffer.seek(0)    
        plt.close()

    def v_plot(pdf,data,title,pept):
        global output_bitmap_v_count
        fig_margin_x_l = 3
        fig_margin_x_r = 3
        fig_margin_y_t = 3
        fig_margin_y_b = 1
        fig_length_x = data.shape[1]
        fig_length_y = data.shape[0]
        fig_x = fig_margin_x_l + fig_length_x + fig_margin_x_r
        fig_y = fig_margin_y_b + fig_length_y + fig_margin_y_t
        cbar_spacer = 0.5  # Gap between heatmap plot and colorbar
        cbar_length  = min(len(colors), fig_length_y)  # 10 or fig_length_x, whichever is smaller
        # make tick labels:
        pept_tick_labels = pept['Start'].map(str) + '-' + pept['End'].map(str)
        time_tick_labels = make_time_tick_labels( data.columns.get_level_values('Exposure') )
        fig = plt.figure(figsize=(fig_x , fig_y), dpi=output_bitmap_dpi)
        ax = plt.axes((fig_margin_x_l/fig_x, fig_margin_y_b/fig_y, fig_length_x/fig_x, fig_length_y/fig_y ))
        ax_4_cbar = plt.axes(((fig_margin_x_l+fig_length_x+cbar_spacer)/fig_x, (fig_margin_y_b + (fig_length_y-cbar_length)/2)/fig_y, cbar_length/len(colors)/fig_x, cbar_length/fig_y ))
        sns.heatmap(data, ax=ax, cmap=colormap, norm=my_norm, xticklabels=time_tick_labels, yticklabels=pept_tick_labels, linewidths=0.30, square=True, cbar_ax=ax_4_cbar, cbar_kws={"orientation": "vertical"})
        plt.sca(ax)
        ax.set_facecolor(c_missing)
        plt.title(title,fontsize=font_size_title)
        plt.xlabel('H/D exchange time')
        plt.ylabel('Peptides')
        ax.xaxis.tick_top()
        ax.xaxis.set_label_position('top')
        ax.tick_params(axis = 'x', labelrotation = 30)
        ax.tick_params(axis = 'y', labelrotation = 0)
        #Placing black line around the plot:
        ax.axhline(y=0, color='k',linewidth=10)
        ax.axhline(y=fig_length_y, color='k',linewidth=10)
        ax.axvline(x=0, color='k',linewidth=10)
        ax.axvline(x=fig_length_x, color='k',linewidth=10)
        # Add separator lines between states:
        states = data.columns.get_level_values('State').unique()
        sep_line_x = 0
        for i in range(len(states)-1):
            exposures = data.loc[:,('Delta_d_uptake','mean',states[i],slice(None))].columns.get_level_values('Exposure')
            sep_line_x += len(exposures)
            ax.axvline(x=sep_line_x, color='k',linewidth=5)
        print(pept_tick_labels)
        print(time_tick_labels)
        pdf.savefig()  # saves the current figure into a pdf page
        if output_bitmap:
            output_bitmap_file = output_bitmap_name + '_v_' + str(output_bitmap_v_count) + '.' + output_bitmap_format
            plt.savefig(output_bitmap_file, dpi=output_bitmap_dpi)
            output_bitmap_v_count += 1
        if PDFgeneration == 1:
            plt.savefig(buffer, format='pdf', dpi=output_bitmap_dpi)
        else:
            plt.savefig(buffer, format='png', dpi=output_bitmap_dpi)
        buffer.seek(0)
        plt.close()   

    
    def w_plot(pdf, data, title, pept, state, data_avg, max_delta, colcutoff):
        # Ensure data_avg is correctly defined and used
        # Ensure global variables are properly managed
        global output_bitmap_h_count
        #print('data avg')
        #print(data_avg)  # Debugging print statement
        unique_exposures = data.columns.get_level_values('Exposure').unique()
        #print('unique exposures')
        #print(unique_exposures)  # Debugging print statement
        numplots = len(unique_exposures)
        #print('data avg info')
        #print(data_avg.info())  # Debugging print statement
        #print('data columns')
        #print(data.columns)
        data_avgrot = data_avg.transpose()
        #print('pept')
        #print(pept)
        first_start = None
        last_end = None
        for exposure in unique_exposures:  # Use unique_exposures instead of exposures
            plt.figure(figsize=(woodsx, woodsy))
            # Extract relevant subset of data for current state and exposure
            subset = data.xs(('Delta_d_uptake', 'mean', state, exposure), level=[None, 'Parameter', 'State', 'Exposure'], axis=1)  
            if colcutopt == 0:
                colcutoff = 0.5
            if nolines == 0:
                plt.axhline(y = 0, color = 'black') #0 line
                plt.axhline(y = colcutoff, color = 'black', linestyle = 'dashed') #Cutoff lines 
                plt.axhline(y = -colcutoff, color = 'black', linestyle = 'dashed')
                plt.axhline(y = 0.75*colcutoff, color = 'black', linestyle = 'dotted') #additional lines
                plt.axhline(y = -0.75*colcutoff, color = 'black', linestyle = 'dotted')
            
            #print('sequence')
            #print(subset.index.get_level_values('Sequence'))
            for peptide in pept.index.get_level_values('Sequence').unique():
                if peptide in subset.index:
                    # Extract mean values for current peptide
                    mean_values = subset.loc[peptide].values
                    #print('mean values')
                    #print(mean_values)
                    # Extract start and end values
                    start_end_values = pept.loc[peptide, ['Start', 'End']].values
                    starts = start_end_values[0]
                    #print('starts')
                    #print(starts)
                    ends = start_end_values[1]
                    #print('ends')
                    #print(ends)
                    # Update first_start and last_end values
                    startsl = []
                    endsl = []
                    startsl.append(start_end_values[0])  # Access 'Start' column directly
                    endsl.append(start_end_values[1])      # Access 'End' column directly
                    if first_start is None:
                        first_start = startsl[0]
                    if last_end is None or last_end < endsl[-1]:
                        last_end = endsl[-1]
                    # Plot the line for current peptide
                    if not pd.isna(mean_values).all():
                        mean_value = mean_values[0]
                        if color_by_heatmap == 1:
                            cmap = colormap
                            norm = my_norm
                            color = cmap(norm(mean_value))
                        elif mean_values > colcutoff:
                            color = woodscolpos
                        elif mean_values < -colcutoff:
                            color = woodscolneg
                        else: 
                            color = woodscolneu
                        plt.plot([starts, ends], [mean_value, mean_value], label=f"{peptide}", color=color, lw=3, path_effects=[pe.Stroke(linewidth=3.5, foreground='black'), pe.Normal()])
                    else:
                        print(f"Skipping plotting for peptide {peptide}: data length mismatch.")
            # Set plot title and labels
            plt.title(f"{title} - State Comparison: {state}, Exposure: {exposure}")
            plt.xlabel('Position')
            plt.ylabel('Change in Deuterium Uptake')
            ax = plt.gca()
            if first_start-(last_end*1/20) <= 0:
                ax.set_xlim([0, last_end+(last_end*1/20)])
            else:
                ax.set_xlim([first_start-(last_end*1/20), last_end+(last_end*1/20)])
            ax.set_ylim([-max_delta-(max_delta/10), max_delta+(max_delta/10)])
            #plt.legend()
            plt.grid(True)
            # Save the plot to the PDF
            pdf.savefig()
            # Save the plot as an image file
            img_buffer = BytesIO()
            if PDFgeneration == 1:
                plt.savefig(img_buffer, format='pdf', dpi=output_bitmap_dpi)
            else:
                plt.savefig(img_buffer, format='png', dpi=output_bitmap_dpi)
            img_buffer.seek(0)
            # Add the image file to the zip archive
            if PDFgeneration == 1:
                zip_file.writestr(f"{title}_State_{state}_Exposure_{exposure}.pdf", img_buffer.read())
            else:
                zip_file.writestr(f"{title}_State_{state}_Exposure_{exposure}.png", img_buffer.read())
            plt.close()

        

    if plot_w:
        all_deltas_grouped = all_deltas.groupby('Protein')
        # Create a ZipFile object to store the plots
        with zipfile.ZipFile("C:\\Users\\kentv\\heatmap\\uploads\\plots.zip", "w") as zip_file:
            for prot, data_subset in all_deltas_grouped:
                for state in all_states:
                    data = data_subset.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                    pept = data_subset.loc[:,['Start','End']]
                    title = 'D uptake difference'
                    w_plot(pdf,data,title,pept,state,data_avg,max_delta,colcutoff)
    elif split_outp_by_prot != None:    
        if split_outp_by_prot == 'all':
            all_deltas_grouped = all_deltas.groupby('Protein')
            for prot, data_subset in all_deltas_grouped:
                if plot_stacked != None:
                    if plot_stacked:
                        data = data_subset.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
                        pept = data_subset.loc[:,['Start','End']]
                        if plot_h:
                            title = 'D uptake difference; Protein: ' + prot + '\nTop to bottom: ' + ', '.join(all_states.to_list())
                            h_plot(pdf,data,title,pept)
                        if plot_v:
                            title = 'D uptake difference; Protein: ' + prot + '\nLeft to right: ' + ', '.join(all_states.to_list())
                            v_plot(pdf,data,title,pept)
                if plot_separate != None:
                    if plot_separate:
                        for state in all_states:
                            data = data_subset.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                            pept = data_subset.loc[:,['Start','End']]
                            title = 'D uptake difference: ' + state + '\nProtein: ' + prot
                            if plot_h:
                                h_plot(pdf,data,title,pept)
                            if plot_v:
                                v_plot(pdf,data,title,pept)
    elif type(split_outp_by_prot) == str and len(split_outp_by_prot)>0:
        print("Variable split_outp_by_prot is set to an unrecognized string '%s'. Either make split_outp_by_prot a list of protein IDs, make it split_outp_by_prot = 'all' to split each protein into a separate plot, or leave it as an empty string (default value) to plot data without splitting by protein ID. No plots will be produced with current settings.\n" % split_outp_by_prot)
    elif type(split_outp_by_prot) == list and len(split_outp_by_prot)>0:
        all_deltas_grouped = all_deltas.groupby('Protein')
        for prot in split_outp_by_prot:
            if type(prot) == tuple:
                data_subset = pd.concat( [all_deltas_grouped.get_group(key) for key in prot] )
                prot_string = '; Proteins: ' + ' '.join(prot)
            else:
                data_subset = all_deltas_grouped.get_group(prot)
                prot_string = '; Protein: ' + prot
            if plot_stacked:
                data = data_subset.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
                pept = data_subset.loc[:,['Start','End']]
                if plot_h:
                    title = 'D uptake difference' + prot_string + '\nTop to bottom: ' + ', '.join(all_states.to_list())
                    h_plot(pdf,data,title,pept)
                if plot_v:
                    title = 'D uptake difference' + prot_string + '\nLeft to right: ' + ', '.join(all_states.to_list())
                    v_plot(pdf,data,title,pept)
            if plot_separate:
                for state in all_states:
                    data = data_subset.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                    pept = data_subset.loc[:,['Start','End']]
                    title = 'D uptake difference: ' + state + prot_string
                    if plot_h:
                        h_plot(pdf,data,title,pept)
                    if plot_v:
                        v_plot(pdf,data,title,pept)
    elif split_outp_chunks:
        chunk_bounds = np.ceil(np.linspace(0,all_deltas.shape[0],split_outp_chunks+1)).astype(int)
        for i in range(split_outp_chunks):
            data_subset = all_deltas.iloc[chunk_bounds[i]:chunk_bounds[i+1]]
            if plot_stacked:
                data = data_subset.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
                pept = data_subset.loc[:,['Start','End']]
                if plot_h:
                    title = 'D uptake difference\nTop to bottom: ' + ', '.join(all_states.to_list())
                    h_plot(pdf,data,title,pept)
                if plot_v:
                    title = 'D uptake difference\nLeft to right: ' + ', '.join(all_states.to_list())
                    v_plot(pdf,data,title,pept)
            if plot_separate:
                for state in all_states:
                    data = data_subset.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                    title = 'D uptake difference: ' + state
                    pept = data_subset.loc[:,['Start','End']]
                    if plot_h:
                        h_plot(pdf,data,title,pept)
                    if plot_v:
                        v_plot(pdf,data,title,pept)
    elif split_outp_by_row:
        split_outp_by_row = [0] + split_outp_by_row + [all_deltas.shape[0]]
        for i in range(len(split_outp_by_row)-1):
            data_subset = all_deltas.iloc[split_outp_by_row[i]:split_outp_by_row[i+1]]
            if plot_stacked:
                data = data_subset.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
                pept = data_subset.loc[:,['Start','End']]
                if plot_h:
                    title = 'D uptake difference\nTop to bottom: ' + ', '.join(all_states.to_list())
                    h_plot(pdf,data,title,pept)
                if plot_v:
                    title = 'D uptake difference\nLeft to right: ' + ', '.join(all_states.to_list())
                    v_plot(pdf,data,title,pept)
            if plot_separate:
                for state in all_states:
                    data = data_subset.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                    title = 'D uptake difference: ' + state
                    pept = data_subset.loc[:,['Start','End']]
                    if plot_h:
                        h_plot(pdf,data,title,pept)
                    if plot_v:
                        v_plot(pdf,data,title,pept)
    else:
        if plot_stacked:
            data = all_deltas.loc[:,('Delta_d_uptake','mean',slice(None),slice(None))]
            pept = all_deltas.loc[:,['Start','End']]
            if plot_h:
                title = 'D uptake difference\nTop to bottom: ' + ', '.join(all_states.to_list())
                h_plot(pdf,data,title,pept)
            if plot_v:
                title = 'D uptake difference\nLeft to right: ' + ', '.join(all_states.to_list())
                v_plot(pdf,data,title,pept)
        if plot_separate:
            for state in all_states:
                data = all_deltas.loc[:,('Delta_d_uptake','mean',state,slice(None))]
                title = 'D uptake difference: ' + state
                pept = all_deltas.loc[:,['Start','End']]
                if plot_h:
                    h_plot(pdf,data,title,pept)
                if plot_v:
                    v_plot(pdf,data,title,pept)
    pdf.close()

    ################################################################################################
    download_pymol = int(request.form.get('download_pymol', 0))
    output_files = []
    
    def download_collect(chain_dict, chain_id, colors, bounds, all_deltas, all_states, buffer, mk_pymol):
        Path(pymol_dir).mkdir(parents=True, exist_ok=True)
        if chain_dict:
            if chain_id:
                print('Both variables chain_dict and chain_id are not empty; Using values from chain_dict, which overrides chain_id.\n')
        else:
            for prot in all_deltas['Protein'].unique():
                chain_dict[prot] = chain_id
        pymol_header = "alter all, b=1000\ncolor %s, all\n\n" %  ('0x' + mc.to_hex(c_missing)[1:])
        curr_color = '0x' + mc.to_hex(colors[0])[1:]
        pymol_footer = "\n\ncolor %s, b<%.3f\n" % (curr_color, bounds[0])
        for i in range(len(bounds)-1):
            curr_color = '0x' + mc.to_hex(colors[i])[1:]
            pymol_footer += "color %s, (b>%.3f or b=%.3f) and b<%.3f\n" % (curr_color, bounds[i], bounds[i], bounds[i+1])
        curr_color = '0x' + mc.to_hex(colors[-1])[1:]
        pymol_footer += "color %s, (b>%.3f or b=%.3f) and b<999\n" % (curr_color, bounds[-1], bounds[-1])
        for state in all_states:
            data = all_deltas.loc[:,('Delta_d_uptake','mean',state,slice(None))]
            time_list = data.columns.get_level_values('Exposure').unique()
            for i in time_list:
                mask = data.loc[:,('Delta_d_uptake', 'mean', state, i)].notna().to_list()
                pymol_str = pd.Series(list(map(mk_pymol, all_deltas['Protein'], all_deltas['Start'], all_deltas['End'], data.loc[:,('Delta_d_uptake', 'mean', state, i)])))[mask]
                pymol_script = pymol_str.to_string(header=False, index=False)
                file_name = "%s_%s.pml" % (state, str(i))
                if pymol_dir:
                    file_name = pymol_dir + "/" + file_name
                f_pymol = open(file_name, 'w')
                print(pymol_header, pymol_script, pymol_footer, file=f_pymol)
                f_pymol.close()
                # Append the file name to the list
                output_files.append(file_name)
        # Create a zip file
        zip_file_name = 'output_files.zip'
        with zipfile.ZipFile(zip_file_name, 'w') as zipf:
            for file in output_files:
                zipf.write(file, os.path.basename(file))
        # Create a zip file containing the Pymol zip and heatmap.png
        combined_buffer = io.BytesIO()
        with zipfile.ZipFile(combined_buffer, 'w') as zipf:
            zipf.write(zip_file_name, os.path.basename(zip_file_name))
            zipf.writestr('heatmap.png', buffer.getbuffer())
        # Set the cursor to the beginning of the combined buffer
        combined_buffer.seek(0)
        # Send the combined zip file as a response
        return send_file(combined_buffer, mimetype='application/zip', as_attachment=True, download_name='heatmap_and_pymol.zip')

    
    if scatter_plot != 2020:
        if file_typeDoH == 1:
            os.remove(input_filecon)
        return send_file(io.BytesIO(scatter_buffer.getvalue()), mimetype='application/zip', as_attachment=True, download_name='scatter_plots.zip')
    else:
        if plot_w:
            zip_filename = "C:\\Users\\kentv\\heatmap\\uploads\\plots.zip"
            pdf_filename = "C:\\Users\\kentv\\heatmap\\uploads\\HDX heatmap.pdf"
            if PDFgeneration == 1:
                return send_file(pdf_filename, download_name='WoodsPlots.pdf', as_attachment=True)
            else:
                return send_file(zip_filename, mimetype='application/zip', download_name='WoodsPlots.zip', as_attachment=True)
        else: 
            if download_pymol == 1:
                if file_typeDoH == 1:
                    os.remove(input_filecon)
                return download_collect(chain_dict, chain_id, colors,bounds, all_deltas, all_states, buffer, mk_pymol)
            else:
                if file_typeDoH == 1:
                    os.remove(input_filecon)
                if PDFgeneration == 1:
                    return_data = io.BytesIO()
                    with open(output_pdf_file, 'rb') as fo:
                        return_data.write(fo.read())
                    return_data.seek(0)
                    os.remove(output_pdf_file)
                    return send_file(return_data, download_name='heatmap.pdf', as_attachment=True)
                else:
                    return send_file(buffer, download_name='heatmap.png', as_attachment=True) 

@app.route('/reset_values', methods=['POST'])
def reset_values():
    return render_template('index.html', output=None)

if __name__ == '__main__':
    app.run(debug=True)


# In[ ]:





# In[ ]:





# # 
