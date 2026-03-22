int main1(){
  int jyk, xc, va, qz, eb, e;
  jyk=1+24;
  xc=(1%60)+60;
  va=(1%9)+2;
  qz=0;
  eb=0;
  e=jyk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eb >= 0;
  loop invariant eb < va;
  loop invariant qz >= 0;
  loop invariant e >= jyk;
  loop invariant e - qz >= jyk;
  loop invariant 0 <= xc - (va*qz + eb);
  loop assigns eb, qz, e;
*/
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