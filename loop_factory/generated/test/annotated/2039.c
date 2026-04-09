int main1(int i){
  int now, o9ae, j59, inu, qvw;
  now=i;
  o9ae=0;
  j59=1;
  inu=5;
  qvw=o9ae;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qvw == o9ae * (o9ae + 1) / 2;
  loop invariant o9ae >= 0;
  loop invariant now == i;
  loop invariant (i < 0) || (o9ae <= i);
  loop invariant j59 >= 1;
  loop invariant inu >= 5;
  loop invariant now == \at(i, Pre);
  loop invariant (\at(i, Pre) >= 0 ==> o9ae <= \at(i, Pre));
  loop assigns o9ae, j59, qvw, inu;
*/
while (1) {
      if (!(o9ae < i && j59 < now)) {
          break;
      }
      o9ae = o9ae + 1;
      j59 = j59 * 2;
      qvw += o9ae;
      inu = inu*inu+inu;
  }
}