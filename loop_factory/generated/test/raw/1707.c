int main1(){
  int wp, e, f, vmw, dca;

  wp=138;
  e=0;
  f=0;
  vmw=3;
  dca=-4;

  while (f<wp) {
      if (f>=wp/2) {
          vmw += 2;
      }
      dca = dca + e;
      f = f + 1;
      dca += 4;
  }

}
