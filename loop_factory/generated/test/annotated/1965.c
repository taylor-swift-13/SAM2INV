int main1(){
  int gv, v1, knt, h, qf2i;
  gv=13;
  v1=0;
  knt=0;
  h=gv;
  qf2i=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant knt == 0;
  loop invariant h == gv;
  loop invariant h != 0;
  loop invariant (v1 == 0) ==> (qf2i == -5);
  loop invariant (v1 > 0) ==> (qf2i % h == 0);
  loop invariant (0 <= v1 && v1 <= gv);
  loop invariant qf2i % 5 == 0;
  loop assigns v1, qf2i, knt;
*/
while (v1 < gv) {
      v1 += 1;
      qf2i = qf2i * h;
      knt = knt * h;
  }
}