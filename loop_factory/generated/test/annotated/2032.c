int main1(int b){
  int q, vn, waw, u, vk;
  q=b+10;
  vn=0;
  waw=b;
  u=0;
  vk=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == b * (vn % 2);
  loop invariant vk == 1 - 2 * (vn % 2);
  loop invariant vn >= 0;
  loop invariant q == b + 10;
  loop invariant vn >= 0 && (q < 0 || vn <= q);
  loop invariant waw - \at(b, Pre) >= -6 * vn;
  loop invariant waw - \at(b, Pre) <= 6 * vn;
  loop assigns u, vn, vk, waw;
*/
while (vn < q) {
      u = u + vk * b;
      vn = vn + 1;
      vk = -vk;
      waw = waw+(u%7);
  }
}