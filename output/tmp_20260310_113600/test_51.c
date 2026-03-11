int main1(){
  int ub, xyu, nju, p, a;
  ub=1+13;
  xyu=ub;
  nju=0;
  p=0;
  a=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= a;
  loop invariant a <= 6;
  loop invariant xyu == ub;
  loop invariant a == 6 - nju;
  loop invariant p == nju*xyu + 6*nju - nju*(nju-1)/2;
  loop invariant 0 <= nju <= ub;
  loop invariant 0 <= p;
  loop invariant p == 20*nju - (nju*(nju-1))/2;
  loop assigns p, nju, a;
*/
while (nju<ub&&a>0) {
      p = p + a;
      nju = nju + 1;
      p += xyu;
      a -= 1;
  }
}