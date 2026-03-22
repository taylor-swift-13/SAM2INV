int main1(){
  int u6r, in, pn, pr1, f2;

  u6r=1;
  in=4;
  pn=0;
  pr1=1;
  f2=-3;

  while (in<=u6r) {
      pn = pn*in;
      if (in<u6r) {
          pr1 = pr1*in;
      }
      f2 = f2 + pr1;
      in += 1;
  }

}
