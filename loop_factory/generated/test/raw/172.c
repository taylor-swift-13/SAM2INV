int main1(int f){
  int f3v, zq, y7, q5o;

  f3v=f;
  zq=0;
  y7=2;
  q5o=1;

  while (zq<=f3v-1) {
      if (y7>=9) {
          q5o = -1;
      }
      if (y7<=2) {
          q5o = 1;
      }
      zq++;
      y7 = y7 + q5o;
  }

}
