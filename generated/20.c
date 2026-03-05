int main20(int v,int w,int b){
  int j, xuu, e7, jr, f19;

  j=v+14;
  xuu=0;
  e7=1;
  jr=1;
  f19=j;

  while (1) {
      if (!(xuu<j)) {
          break;
      }
      xuu += 2;
      jr += 2;
      e7 += 2;
      v = v+(jr%3);
      b += 1;
      f19 = f19+(xuu%8);
  }

}
