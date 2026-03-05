int main1(){
  int r39, psw, c;

  r39=(1%9)+16;
  psw=0;
  c=0;

  while (psw<r39) {
      if (psw%2==0) {
          if (c>0) {
              c--;
              c = c + 1;
          }
      }
      else {
          if (c>0) {
              c--;
              c = c + 1;
          }
      }
      psw++;
      c += 4;
  }

}
