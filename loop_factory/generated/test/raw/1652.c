int main1(int v){
  int v6, hp4r, at, ud;

  v6=36;
  hp4r=0;
  at=0;
  ud=3;

  while (1) {
      if (!(hp4r<v6&&ud>0)) {
          break;
      }
      at = at + ud;
      hp4r++;
      ud -= 1;
  }

}
