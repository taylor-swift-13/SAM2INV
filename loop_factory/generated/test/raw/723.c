int main1(int d){
  int ahk, sr, zpy, qg, t;

  ahk=d;
  sr=ahk+3;
  zpy=0;
  qg=(d%28)+10;
  t=sr;

  while (qg>zpy) {
      qg = qg - zpy;
      t = t + sr;
      zpy++;
  }

}
