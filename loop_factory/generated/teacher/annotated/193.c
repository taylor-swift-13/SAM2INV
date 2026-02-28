int main1(int p,int q){
  int e, w, u, k, f;

  e=17;
  w=e;
  u=e;
  k=p;
  f=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w + 4*u == 85;
  loop invariant u >= 17;

  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre) &&
                   q == \at(q, Pre) &&
                   u >= 17 &&
                   f >= 17 &&
                   w <= 17 &&
                   w + f == 34 &&
                   w == 17 - 4*(u - 17) &&
                   ((17 - w) % 4) == 0;
  loop invariant w >= 1;
  loop invariant w <= 17;
  loop invariant f >= 17;
  loop assigns u, f, w;
*/
while (w>3) {
      u = u+1;
      f = f+4;
      w = w-4;
  }

}
