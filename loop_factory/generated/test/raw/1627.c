int main1(){
  int ma, lg, lr, wim;

  ma=80;
  lg=0;
  lr=lg;
  wim=ma;

  while (1) {
      if (!(lg < ma)) {
          break;
      }
      lr--;
      wim = wim + 1;
      lr = lr+wim+wim;
      lg = ma;
  }

}
