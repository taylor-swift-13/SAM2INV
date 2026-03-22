int main1(){
  int fhl, u2, p, r602, js;

  fhl=1-7;
  u2=0;
  p=2;
  r602=1;
  js=3;

  while (u2<=fhl) {
      p = p*u2;
      if (u2<fhl) {
          r602 = r602*u2;
      }
      u2 += 1;
      js += r602;
  }

}
