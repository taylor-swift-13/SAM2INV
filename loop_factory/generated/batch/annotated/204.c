int main1(int p,int q){
  int i, b, v;

  i=53;
  b=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -1 || v == 0;
  loop invariant 0 <= b;
  loop invariant b <= i;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == 53;
  loop invariant (b == 0 && v == -1) || (b >= 1 && v == 0);
  loop invariant (b == 0 ==> v == -1) && (b >= 1 ==> v == 0);
  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant ((b == 0 && v == -1) || (b >= 1 && v == 0));
  loop assigns b, v;
*/
while (b<=i-1) {
      v = v*v+v;
      b = b+1;
  }

}
