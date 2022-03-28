datatype seasoning = Salt | Peper;

datatype num = Zero
             | One_more_than of num;

datatype 'a open_faced_sandwich = Bread of 'a
				| Slice of 'a open_faced_sandwich;
