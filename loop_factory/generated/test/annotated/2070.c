int main1(int n){
  int cb, urw, xi;
  cb=n;
  urw=0;
  xi=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cb == \at(n, Pre);
  loop invariant urw >= 0;
  loop invariant (cb >= 0 ==> urw <= cb);
  loop invariant 2*(xi + 3) == (urw*(urw - 1));
  loop invariant 6*(n - \at(n, Pre) + 3*urw) == (urw*(urw - 1)*(urw + 1));
  loop invariant 0 <= urw;
  loop invariant xi == -3 + (urw*(urw-1))/2;
  loop invariant n == \at(n, Pre) + (-3*urw) + (urw*(urw-1)*(urw+1))/6;
  loop invariant xi == (-3 + ((urw*(urw-1))/2));
  loop invariant n == (\at(n, Pre) + (((urw*(urw+1)*(urw-1))/6) - 3*urw));
  loop invariant xi == (-3) + (urw*(urw-1))/2;
  loop invariant n == \at(n, Pre) + (urw*(urw-1)*(urw+1))/6 - 3*urw;
  loop invariant (urw*(urw-1)) == 2*(xi + 3);
  loop invariant 6*(n - \at(n, Pre)) == (urw*urw*urw) - 19*urw;
  loop assigns n, urw, xi;
*/
while (urw < cb) {
      xi += urw;
      n = n + xi;
      urw += 1;
  }
}