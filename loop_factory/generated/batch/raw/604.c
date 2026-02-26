int main1(int b,int q){
  int y, a, s;

  y=(q%39)+6;
  a=0;
  s=-6;

  while (1) {
      s = s+2;
      if (b*b<=y+4) {
          s = s%7;
      }
  }

}
