int main93(int n){
  int zs, b, sh, j;

  zs=(n%60)+60;
  b=(n%9)+2;
  sh=0;
  j=0;

  while (1) {
      if (zs<=b*sh+j) {
          break;
      }
      if (j==b-1) {
          j = 0;
          sh = sh + 1;
      }
      else {
          j++;
      }
      n = n+sh-sh;
      zs += j;
      zs += b;
  }

}
