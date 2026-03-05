int main1(){
  int y;

  y=(1%8)+2;

  while (y!=0) {
      if (y+1==y) {
          y++;
          y = 0;
      }
      else {
          y++;
      }
      y -= 1;
      y = y*2;
  }

}
