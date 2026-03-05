int main1(int a,int q){
  int c1nx, mk, o, d9;

  c1nx=a+14;
  mk=c1nx;
  o=12;
  d9=0;

  while (mk<c1nx) {
      if (mk%2==0) {
          if (o>0) {
              o--;
              d9++;
          }
      }
      else {
          if (d9>0) {
              d9 -= 1;
              o = o + 1;
          }
      }
      mk = mk + 1;
      a = a + d9;
      q = q + q;
  }

}
