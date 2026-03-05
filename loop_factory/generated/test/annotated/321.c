int main1(int d,int i){
  int r5h, ig, wwl;
  r5h=54;
  ig=0;
  wwl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r5h == 54;
  loop invariant d == \at(d, Pre);
  loop invariant i == \at(i, Pre);
  loop invariant 0 <= wwl <= r5h && (wwl == 0 || wwl == 1) && ig >= 0;
  loop assigns wwl, ig;
*/
while (wwl>0&&wwl<=r5h) {
      if (wwl>wwl) {
          wwl -= wwl;
      }
      else {
          wwl = 0;
      }
      wwl++;
      ig++;
  }
}