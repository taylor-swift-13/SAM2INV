int main1(int a){
  int iu, xy;

  iu=68;
  xy=0;

  while (xy<iu) {
      if (xy%10==0) {
          xy++;
      }
      else {
          if (xy%6==0) {
              xy++;
          }
          else {
              if (xy%7==0) {
                  xy++;
              }
              else {
                  xy++;
              }
          }
      }
      xy++;
      a = (a+xy)%7;
  }

}
