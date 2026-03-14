int main1(int z,int k){
  int nm, w, e, vb5, o6q, p5a;
  nm=39;
  w=0;
  e=8;
  vb5=0;
  o6q=1;
  p5a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e + vb5 == 8;
  loop invariant 1 <= o6q;
  loop invariant 0 <= w;
  loop invariant w <= nm;
  loop invariant o6q == w + 1;
  loop invariant 0 <= e <= 8;
  loop invariant 0 <= vb5 <= 8;
  loop assigns e, o6q, vb5, w, p5a;
*/
while (e>0&&w<nm) {
      if (e<=o6q) {
          p5a = e;
      }
      else {
          p5a = o6q;
      }
      e -= p5a;
      o6q += 1;
      vb5 += p5a;
      w += 1;
  }
}