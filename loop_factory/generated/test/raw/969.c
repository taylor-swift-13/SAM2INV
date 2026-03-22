int main1(){
  int x, bg, d;

  x=(1%20)+5;
  bg=(1%20)+5;
  d=(1%20)+5;

  while (1) {
      if (!(x>=1)) {
          break;
      }
      if (bg>0) {
          if (d>0) {
              x--;
              bg--;
              d -= 1;
          }
      }
      bg = bg + 5;
  }

}
