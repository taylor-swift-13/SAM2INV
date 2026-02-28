int main1(int a,int k){
  int h, r, p, w;

  h=k+14;
  r=h;
  p=h;
  w=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == k + 14;
  loop invariant r <= h;
  loop invariant p == 3*r - 2*h;
  loop invariant p <= h;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == h + 3*(r - h);
  loop invariant p - 3*r == -2*h;
  loop assigns p, r;
*/
while (1) {
      if (r>=h) {
          break;
      }
      p = p+2;
      r = r+1;
      p = p+1;
  }

}
