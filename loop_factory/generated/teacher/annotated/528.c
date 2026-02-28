int main1(int k,int p){
  int n, v, h, e;

  n=k;
  v=0;
  h=-8;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(k, Pre);
  loop invariant 0 <= v;

  loop invariant h == -8 + 3*v;
  loop invariant p == \at(p, Pre);
  loop invariant v >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == k;
  loop assigns v, h;
*/
while (1) {
      if (v>=n) {
          break;
      }
      h = h+2;
      v = v+1;
      h = h+1;
  }

}
