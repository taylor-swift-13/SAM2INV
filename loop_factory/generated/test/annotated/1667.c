int main1(){
  int b, qy, zy0, kpi9, zh;
  b=1;
  qy=b;
  zy0=0;
  kpi9=b;
  zh=qy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kpi9 <= zy0 + 2;
  loop invariant b == 1;
  loop invariant zy0 - 7*zh + 7 == 0;
  loop invariant zy0 >= 0;
  loop invariant zy0 <= b + 6;
  loop assigns kpi9, zh, zy0;
*/
while (zy0+7<=b+7-1) {
      kpi9 = zy0+2;
      zy0 = zy0 + 7;
      zh += b;
  }
}