int main1(int l){
  int in2f, c, o, uq, i, d1, be;

  in2f=55;
  c=in2f;
  o=2;
  uq=2;
  i=0;
  d1=3;
  be=0;

  while (c<in2f) {
      if (c%3==0) {
          if (o>0) {
              o--;
              i = i + 1;
          }
      }
      else {
          if (o<d1) {
              o = o + 1;
              uq += 1;
          }
      }
      be++;
      c = c + 1;
      d1 = d1 + be;
  }

}
