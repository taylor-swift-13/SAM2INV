int main1(){
  int q, yh, m5, a65, ur;

  q=(1%28)+18;
  yh=-6;
  m5=1;
  a65=0;
  ur=yh;

  while (1) {
      if (!(m5<q)) {
          break;
      }
      m5 = 2*m5;
      a65 = (1)+(a65);
      ur = ur*2+(a65%7)+2;
  }

}
