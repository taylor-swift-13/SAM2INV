int main142(int a){
  int sys, t0, q, rx, up, dlos;

  sys=a+3;
  t0=sys;
  q=t0;
  rx=4;
  up=sys;
  dlos=sys;

  while (1) {
      if (!(t0>=1)) {
          break;
      }
      rx = rx + up;
      up = up + q;
      if (up+7<sys) {
          dlos += t0;
      }
      t0 = t0 - 1;
  }

}
