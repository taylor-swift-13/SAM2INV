int main1(int a,int b,int k,int n){
  int t, i, v, w, p, z, y, o;

  t=48;
  i=0;
  v=-5;
  w=i;
  p=i;
  z=8;
  y=b;
  o=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 8;
  loop invariant z <= t + 1;
  loop invariant p == 2*(z - 8);
  loop invariant w == (z - 8)*(z - 9);
  loop invariant v == -5 + (z - 8) + ((z - 8)*(z - 9)*(z - 10))/3;
  loop invariant 3*v == (z - 9)*(z - 8)*(z - 10) + 3*(z - 8) - 15;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 3*v == (z-8)*(z-8)*(z-8) - 3*(z-8)*(z-8) + 5*(z-8) - 15;
  loop invariant t == 48;
  loop invariant v == -5 + ((z - 8)*(z - 9)*(z - 10))/3 + (z - 8);
  loop invariant 3*v == (z - 9)*(z - 8)*(z - 10) + 3*z - 39;
  loop assigns v, w, p, z;
*/
while (z<=t) {
      v = v+w;
      w = w+p;
      p = p+2;
      z = z+1;
      v = v+1;
  }

}
