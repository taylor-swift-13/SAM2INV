int main1(){
  int ng, ok, e, plw, qaj;
  ng=1*3;
  ok=1;
  e=20;
  plw=3;
  qaj=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ng == (ok*4) - 1;
  loop invariant e % 4 == 0;
  loop invariant plw >= 0;
  loop invariant qaj >= -4;
  loop invariant 3*(qaj + 4) == 4*(e - 20);
  loop invariant ok == 1;
  loop assigns e, plw, qaj, ng;
*/
while (1) {
      if (!(ok*4<=ng)) {
          break;
      }
      e = e*4;
      plw = plw/4;
      qaj = qaj + e;
      ng = (ok*4)-1;
  }
}