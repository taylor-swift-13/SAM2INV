int main1(){
  int vfo, t64o, t, y2d;

  vfo=8;
  t64o=vfo;
  t=vfo;
  y2d=0;

  while (t64o-1>=0) {
      if (t64o<vfo/2) {
          t = t + y2d;
      }
      else {
          t += 1;
      }
      t64o = t64o + 1;
  }

}
