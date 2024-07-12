# ChicletPro
Code for HDX Heatmapping Website

This is built to run using Azure webhosting and Flask in python
  Important changes to run locally would be:
      Removing references to Azure blob storage - this is where generated files are stored, this should be changed to local storage
      Flask calls for variables from an HTML template (in template file)
      Remove App definitions (app routes before definitions) 
        Can essentially copy out the code from within the generate_pdf def, ensuring dependencies are defined at top of code and all variables are set manually in the code
      input_csv_file should be a path to the input files local storage location eg input_csv_file = r"C:\Users\kentv\Downloads\example HDX Data (1).csv"

Alternatively there is a seperate folder - local file
  This is the original script generated by Dr. Algirdas Velyvis. It requires manual input of all values, as well as values to decide which plotting method to use. 
      In depth explanation has been provided within the script describing what each variable is and how it should be used
  Of note, this script can not generate Woods Plots, as this was a later addition after transitioning to Azure and Flask
  Additionally, this script only recognizes DynamX cluster files, and not outputs from HDeXaminer
    A seperate python script has been provided to convert HDeXaminer files to DynamX
      
