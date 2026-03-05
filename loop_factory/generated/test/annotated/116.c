int main1(int j){
  int gi5, opo, ue, lt3;
  gi5=23;
  opo=0;
  ue=0;
  lt3=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant opo == lt3 - 1;
  loop invariant j == \at(j, Pre);
  loop invariant gi5 == 23;
  loop invariant 0 <= ue <= lt3;
  loop invariant 1 <= lt3 <= gi5 + 1;
  loop assigns ue, lt3, opo;
*/
for (; ue>0&&lt3<=gi5; opo++) {
      if (ue>lt3) {
          ue = ue - lt3;
      }
      else {
          ue = 0;
      }
      ue += 1;
      lt3 += 1;
  }
}