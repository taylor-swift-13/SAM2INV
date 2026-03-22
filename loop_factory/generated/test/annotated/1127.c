int main1(){
  int cp, vh5, ujb, vis, k, s;
  cp=55;
  vh5=cp;
  ujb=(1%40)+2;
  vis=0;
  k=8;
  s=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 8;
  loop invariant cp == 55;
  loop invariant 1 <= ujb <= 55;
  loop invariant 0 <= vis <= 55;
  loop assigns vis, k, ujb;
*/
while (ujb!=vis) {
      vis = ujb;
      k = k+vis-vis;
      ujb = (ujb+cp/ujb)/2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 8;
  loop invariant cp == 55;
  loop invariant 1 <= vh5;
  loop invariant vh5 <= 55;
  loop invariant 1 <= s <= 55;
  loop invariant ujb > 0;
  loop assigns vh5, s, ujb;
*/
while (1) {
      if (!(s!=vh5)) {
          break;
      }
      vh5 = s;
      s = (s+cp/s)/2;
      ujb = ujb + k;
  }
}