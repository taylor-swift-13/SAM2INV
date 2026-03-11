int main1(int c){
  int hl, o2o8, ptk, i3;
  hl=72;
  o2o8=0;
  ptk=0;
  i3=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ptk == 3*o2o8;
  loop invariant 0 <= o2o8;
  loop invariant o2o8 <= hl;
  loop invariant i3 - ptk == 3;
  loop assigns i3, ptk, o2o8;
*/
while (1) {
      if (!(o2o8<hl)) {
          break;
      }
      i3 = i3 + 3;
      ptk = ptk + 3;
      o2o8++;
  }
}