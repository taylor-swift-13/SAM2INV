int main1(){
  int wb, s7k, hd, sy, bv, w;

  wb=30;
  s7k=3;
  hd=0;
  sy=s7k;
  bv=12;
  w=s7k;

  while (1) {
      if (!(hd<=wb-1)) {
          break;
      }
      sy = hd+4;
      hd = hd + 3;
      bv += hd;
  }

  while (s7k<w) {
      s7k++;
      bv = bv + 1;
      sy = sy + s7k;
  }

}
