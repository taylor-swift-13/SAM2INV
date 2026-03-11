int main1(int a,int k){
  int r, u, i, o, v;

  r=(k%8)+14;
  u=r;
  i=r;
  o=-5;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 3*r - 2*u;
  loop invariant (0 <= u) && (u <= r);
  loop invariant r <= i <= 3*r;
  loop invariant o == -5 + (r - u)*r + (r - u)*(r - u + 1);
  loop invariant r == (k % 8) + 14;
  loop invariant o == -5 + (r - u) * (2*r - u + 1);
  loop invariant 0 <= u;
  loop invariant u <= r;
  loop invariant i + 2*u == 3 * ((k % 8) + 14);
  loop invariant i >= ((k % 8) + 14);
  loop invariant o == -5 + (((k % 8) + 14) - u) * ((k % 8) + 14) + (((k % 8) + 14) - u) * (((k % 8) + 14) - u + 1);
  loop invariant r == ((k % 8) + 14);

  loop invariant u >= 0 && i >= r;
  loop invariant 2*u + i == 3*( (\at(k, Pre) % 8) + 14 );
  loop invariant u >= 0;
  loop invariant i <= 3*( (\at(k, Pre) % 8) + 14 );
  loop assigns i, o, u;
*/
while (u>0) {
      i = i+2;
      o = o+i;
      u = u-1;
  }

}
