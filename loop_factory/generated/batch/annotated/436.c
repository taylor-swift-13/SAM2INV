int main1(int a,int k){
  int l, j, r, v;

  l=23;
  j=1;
  r=l;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 23;
  loop invariant (r == 23 || r == 0) && (j >= 1) && (j <= l) && (a == \at(a, Pre)) && (k == \at(k, Pre));
  loop invariant j <= l;
  loop invariant r >= 0;
  loop invariant r <= l;
  loop invariant j >= 1;
  loop invariant j <= 16;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == 1 || j == 2 || j == 4 || j == 8 || j == 16;
  loop invariant r == 23 || (0 <= r && r <= 7);
  loop invariant j <= 32;
  loop assigns r, j;
*/
while (j<=l/2) {
      r = r*r+r;
      r = r%8;
      j = j*2;
  }

}
