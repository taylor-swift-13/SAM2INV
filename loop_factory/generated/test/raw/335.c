int main1(){
  int to, tk, g, fx, ik;

  to=1*3;
  tk=to;
  g=0;
  fx=0;
  ik=0;

  while (1) {
      if (!(fx<to)) {
          break;
      }
      g++;
      fx = fx + 1;
      ik += fx;
  }

  while (tk<to) {
      tk++;
      fx = fx + 1;
      fx = fx + 1;
  }

}
