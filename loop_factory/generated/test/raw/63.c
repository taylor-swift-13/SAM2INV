int main1(){
  int mc, z0r, g, yl;

  mc=(1%30)+17;
  z0r=2;
  g=mc;
  yl=0;

  while (1) {
      yl -= 1;
      g++;
      yl = yl + yl;
      z0r += 1;
      if (z0r>=mc) {
          break;
      }
  }

}
