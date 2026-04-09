int main1(){
  int ivns, tf0d, a7, bh, g;

  ivns=56;
  tf0d=ivns+6;
  a7=0;
  bh=12;
  g=13;

  while (1) {
      if (!(tf0d>1)) {
          break;
      }
      a7 = a7*4;
      bh = bh/4;
      g = bh*bh;
      tf0d = tf0d/2;
  }

}
