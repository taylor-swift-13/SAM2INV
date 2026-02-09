/*@ requires 1==1;*/
int main1(){

  int sn, a, x;
  
  sn = 0;
  x = 0;

  while(unknown()) {
    if (x<10) {
        sn = sn + a;
        x++;
    }
  }
  /*@ assert sn == x*a || sn == 0;*/
}

