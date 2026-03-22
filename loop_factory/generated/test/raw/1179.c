int main1(){
  int jyk, xc, va, qz, eb, e;

  jyk=1+24;
  xc=(1%60)+60;
  va=(1%9)+2;
  qz=0;
  eb=0;
  e=jyk;

  while (1) {
      if (xc<=va*qz+eb) {
          break;
      }
      if (eb==va-1) {
          eb = 0;
          qz++;
      }
      else {
          eb++;
      }
      e = (qz)+(e);
  }

}
