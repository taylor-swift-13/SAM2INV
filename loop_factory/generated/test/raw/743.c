int main1(int z,int k){
  int d6, f;

  d6=0;
  f=(z%28)+10;

  while (f>d6) {
      f -= d6;
      d6 = (1)+(d6);
      z += f;
  }

}
