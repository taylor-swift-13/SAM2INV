int main1(int a,int k,int n,int p){
  int w, i, y, h, f;

  w=n+15;
  i=0;
  y=-4;
  h=2;
  f=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant y == i - 4;
  loop invariant h == (i*i - 7*i + 4)/2;
  loop invariant a == \at(a, Pre) &&
                   k == \at(k, Pre) &&
                   n == \at(n, Pre) &&
                   p == \at(p, Pre);
  loop invariant w == \at(n, Pre) + 15 &&
                   i == y + 4 &&
                   h == (y*y + y)/2 - 4 &&
                   y >= -4;
  loop invariant i >= 0;
  loop invariant 2*h == i*i - 7*i + 4;
  loop invariant w == n + 15;
  loop assigns y, h, i;
*/
while (1) {
      y = y+1;
      h = h+y;
      i = i+1;
  }

}
