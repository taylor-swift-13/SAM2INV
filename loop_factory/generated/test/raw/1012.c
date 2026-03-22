int main1(){
  int pr, a99, vukl, kyr, gc73, a;

  pr=1;
  a99=pr;
  vukl=38;
  kyr=0;
  gc73=1;
  a=0;

  while (1) {
      if (!(vukl>0&&a99<pr)) {
          break;
      }
      if (vukl<=gc73) {
          a = vukl;
      }
      else {
          a = gc73;
      }
      kyr = kyr + a;
      a99++;
      gc73 += 1;
      vukl = vukl - a;
  }

}
