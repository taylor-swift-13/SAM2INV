int main1(int b,int n,int k){
  int i0a, kx;
  i0a=3;
  kx=(n%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kx <= (\at(n,Pre) % 20) + 5;
  loop invariant n == \at(n,Pre) + i0a * (k - \at(k,Pre));
  loop invariant b == \at(b,Pre) + 3 * (k - \at(k,Pre));
  loop invariant n - b == (\at(n,Pre) - \at(b,Pre));
  loop invariant k + kx == \at(k,Pre) + ((\at(n,Pre) % 20) + 5);
  loop invariant n >= \at(n,Pre);
  loop invariant b >= \at(b,Pre);
  loop invariant i0a == 3;
  loop invariant kx + k == (\at(n, Pre) % 20 + 5) + \at(k, Pre);
  loop invariant n - \at(n,Pre) == i0a * (k - \at(k,Pre));
  loop invariant n - i0a * k == \at(n, Pre) - i0a * \at(k, Pre);
  loop invariant kx == ((\at(n, Pre) % 20) + 5) - (k - \at(k, Pre));
  loop invariant 0 <= k - \at(k, Pre);
  loop assigns kx, b, n, k;
*/
while (1) {
      if (!(kx>0)) {
          break;
      }
      kx = kx - 1;
      b = b + 3;
      n += i0a;
      k += 1;
  }
}