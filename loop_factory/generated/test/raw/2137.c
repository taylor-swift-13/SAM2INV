int main1(int m){
  int wpo4, zbr, gib, in7, b;

  wpo4=m;
  zbr=m;
  gib=wpo4;
  in7=7;
  b=(m%6)+2;

  while (1) {
      if (in7>=wpo4) {
          break;
      }
      zbr = zbr*b+m;
      gib = gib*b;
      in7 = in7 + 1;
  }

}
