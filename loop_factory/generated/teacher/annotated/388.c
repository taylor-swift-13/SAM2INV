int main1(int k,int p){
  int c, m, j, b;

  c=k+24;
  m=0;
  j=k;
  b=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(k, Pre) + 24;
  loop invariant k == \at(k, Pre);
  loop invariant m == 0;
  loop invariant p == \at(p, Pre);
  loop invariant c == k + 24;
  loop assigns m;
*/
while (1) {
      m = m;
  }

}
