#include <stdio.h>
#include <stdint.h>
#include <string.h>

uint32_t out[20][32];
uint32_t in[18][20];
uint32_t sync_word[25]= {0x6b3c87f2, 0x308d0020, 0x7dbf1b89, 0x4297ec79,
                        0x0f27413e, 0x5e179c8d, 0x7c76be26, 0x073946cf, 0x54475d7a,
                        0x2812e82b, 0x06282513, 0x092d4b8b, 0x140bf875, 0x15bfdb85,
                        0x62c8f60f, 0x790fc2b7, 0x34241c66, 0x57130464, 0x2feec405, 
                        0x4a661b7f, 0x47bcabbe, 0x7e7bfcc4, 0x76c40ab4, 0x381dc271, 0x0afa2c4b};
uint32_t data_pilots[18][25];
uint8_t data_pilots_bit[20][1024]; // Store bits as bytes for preprocessing to make things easier

int main(){
    int bit_counter = 0;
    int byte_counter = 0;
    int subc_counter = 0;
    int count_in = 0;
    FILE *fp = fopen("input.txt","w");


    for(int i = 0; i<20 ; i++)
        memset(out[i], 0, 32 * sizeof(uint32_t));
    for(int i =0 ; i< 18 ; i++){
        for(int j = 0; j< 20; j++){
            in[i][j] = rand();
            fprintf(fp, "%08x ", in[i][j]);
        }
    }
    fclose(fp);
    for(int i = 0; i < 20 ; i++)
        memset(data_pilots[i], 0, 25 * sizeof(uint32_t));

    for(int i = 0 ; i < 20 ; i++){
        bit_counter = 0;
        byte_counter = 0;
        subc_counter = 0;
        for(int j = 0; j < 1024; j++){
            if((j < 111) || (j > 911) || (j == 511) || (j == 512))
                data_pilots_bit[i][j] = 0;
            else{
                if(i % 10 != 0){ // Add data
                    if(subc_counter % 10 == 0)
                        data_pilots_bit[i][j] = 1;
                    else if(subc_counter % 10 == 5)
                        data_pilots_bit[i][j] = 0;
                    else{
                        data_pilots_bit[i][j] = ((in[count_in][byte_counter] >> bit_counter) & 0x01) ? 1 : 0;
                        bit_counter++;
                        if(bit_counter >= 32){
                            bit_counter = 0;
                            byte_counter++;
                        }
                    }
                    subc_counter++;
                }
                else{ // Add sync word
                    data_pilots_bit[i][j] = ((sync_word[byte_counter] >> bit_counter) & 0x01) ? 1 : 0;
                    bit_counter++;
                    if(bit_counter >= 32){
                        bit_counter = 0;
                        byte_counter++;
                    }
                }
            }
        }
        if(i % 10 !=0)
            count_in++;
    }
    bit_counter = 0;
    byte_counter = 0;
    uint8_t bit;
    fp = fopen("output.txt","w");
    for(int i = 0 ; i < 20 ; i++){
        for(int k = 0; k < 1024 ; k++){
            bit = (data_pilots_bit[i][k]) ? 1 : 0;
            out[i][k/32] |= ((bit & 0x1) << (k%32));
            if(k%32 == 31)
                fprintf(fp, "%08x ", out[i][k/32]);
        }
    }
    fclose(fp);
}
