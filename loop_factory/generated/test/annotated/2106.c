int main1(){
  int v2, j3k, el4s, el, av;
  v2=1+9;
  j3k=1;
  el4s=0;
  el=0;
  av=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= j3k;
  loop invariant j3k <= v2;
  loop invariant (el == 0) || (el == 4);
  loop invariant el4s >= 0;
  loop invariant el4s <= av;
  loop invariant (j3k == 1) || (j3k == v2);
  loop invariant (j3k < v2) ==> (el == 0 && el4s == 0);
  loop invariant (el4s == 0) || (el4s == av);
  loop invariant (j3k < v2) <==> (el == 0);
  loop assigns el4s, el, j3k;
*/
while (1) {
      if (!(j3k < v2)) {
          break;
      }
      el4s = el4s + av / (j3k++);
      el += 4;
      j3k = v2;
  }
}