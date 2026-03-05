int main1(int p){
  int fs, a;

  fs=(p%11)+15;
  a=0;

  while (a<fs) {
      a += 2;
      if (a<=a) {
          a = a;
      }
      p = p + a;
  }

}
