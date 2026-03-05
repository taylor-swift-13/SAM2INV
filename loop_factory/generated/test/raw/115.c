int main1(int s){
  int sdq, eit, u4ud;

  sdq=(s%18)+6;
  eit=sdq;
  u4ud=0;

  while (eit<sdq) {
      u4ud += 1;
      if (u4ud>=5) {
          u4ud = u4ud - 5;
          u4ud += 1;
      }
      eit++;
  }

}
