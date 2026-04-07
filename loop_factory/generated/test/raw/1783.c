int main1(){
  int dat, md1g, x, cn;

  dat=(1%60)+60;
  md1g=(1%9)+2;
  x=0;
  cn=0;

  while (1) {
      if (dat<=md1g*x+cn) {
          break;
      }
      if (cn==md1g-1) {
          cn = 0;
          x = x + 1;
      }
      else {
          cn += 1;
      }
      dat = dat + cn;
  }

}
