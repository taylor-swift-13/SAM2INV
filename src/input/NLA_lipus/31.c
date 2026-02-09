/*@ requires n > 0;*/
int main1(){

  int i, n, sn, a;
  
  sn = 0;
  i = 0;

  while(i < n) {
    sn = sn + a;
    i++;
  }
  /*@ assert sn == n*a || sn == 0;*/
}

