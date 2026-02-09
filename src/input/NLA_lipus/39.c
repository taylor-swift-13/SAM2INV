/*@ requires n > 0;*/
int main1(){

  int n;
  


  while (i <= n) {
        sum = sum + i;  
        i = i + 1;      
    }
  /*@ assert sum == (n * (n + 1)) / 2;*/
}

