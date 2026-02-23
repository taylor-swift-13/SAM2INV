int main1(int b,int p){
  int l, j, v, f, z;

  l=30;
  j=l;
  v=p;
  f=1;
  z=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(p, Pre);
  loop invariant 0 <= j && j <= l;
  loop invariant l == 30;
  loop invariant f == 1 && z == -2;
  loop invariant p == \at(p, Pre) && b == \at(b, Pre);
  loop invariant v == p;
  loop invariant j >= 0;
  loop invariant j <= 30;
  loop invariant f == 1;
  loop invariant z == -2;
  loop invariant j <= l;
  loop invariant p == \at(p, Pre);
  loop invariant v == \at(p, Pre) + (l - j) * (f + z + 1);
  loop invariant b == \at(b, Pre);
  loop assigns v, j;
*/
while (j>0) {
      v = v+f+z;
      v = v+1;
      j = j-1;
  }

}
