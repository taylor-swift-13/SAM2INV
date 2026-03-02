int main1(int b,int k){
  int r, u, w;

  r=b-4;
  u=0;
  w=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == b - 4;
  loop invariant 0 <= u;
  loop invariant (r >= 0) ==> (u <= r);
  loop invariant w >= 5;
  loop invariant r == \at(b, Pre) - 4;
  loop invariant u >= 0 && w - u >= 5;
  loop invariant u >= 0;
  loop invariant u == 0 || u <= r;
  loop invariant w >= 5 + u;
  loop invariant w <= 5 + u + (u*(u-1))/2;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant w >= 5 + u && w <= 5 + u + u*(u-1)/2;
  loop invariant (r >= 0) ==> (0 <= u && u <= r) && w >= 5 + u;

  loop invariant r == \at(b, Pre) - 4 && b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant u >= 0 && w >= 5 + u;
  loop invariant w - u >= 5;

  loop assigns w, u;
*/
while (u+1<=r) {
      if (u+7<=k+r) {
          w = w+u;
      }
      w = w+1;
      u = u+1;
  }

}
